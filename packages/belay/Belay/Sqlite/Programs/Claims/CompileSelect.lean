import Belay.Sqlite.Programs.Claims.LastOutput
import Belay.Sqlite.Programs.Claims.ReadStepRule
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution
import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Programs.Claims.CompiledDelete

set_option doc.verso true

namespace Belay.Sqlite
open Model hiding Database
open CompiledScript

/-- The profile of an unordered SELECT that succeeds with a given bag of rows.
The actual output is the normalized bag, and it is the sole permitted output. -/
def LastOutputPlan.rowBag (rows : List (List Value)) : Option Output × (Option Output → Prop) :=
  let last := some (Output.rows (Resolved.normalForm rows))
  (last, fun o => last = o)

/-- For any two bags of rows, their deterministic last-output profiles agree exactly when
the lists are permutations. Proof sketch: compare the actual outputs and use the
characterization of {name}`Resolved.normalForm_eq_iff_perm` in both directions. -/
theorem LastOutputPlan.rowBag_eq_iff (xs ys : List (List Value)) :
    rowBag xs = rowBag ys ↔ xs.Perm ys := by
  constructor
  · intro same
    have actual := congrArg Prod.fst same
    simpa only [rowBag, Option.some.injEq, Output.rows.injEq, Resolved.normalForm_eq_iff_perm] using actual
  · intro perm
    simp only [rowBag, (Resolved.normalForm_eq_iff_perm xs ys).mpr perm]

/-- Compile the table, its selection and its projection separately so preceding writes
can fuse their restrictions with the SELECT before the scan runs. -/
private def selectPlan (pos : Nat) (q : Resolved.Query) (args : List Value) : Plan :=
  ⟨pos, Filter.whereClause args false q.filter, .project q.columns args⟩

/-- The plan produces the model's projected bag. Proof sketch: use the filter acceptance
law and the correctness of each compiled scalar. -/
private theorem selectPlan_eq (pos : Nat) (q : Resolved.Query) (args : List Value) (src : Sources) :
    (selectPlan pos q args).run src = .rows (Resolved.normalForm
      ((Resolved.filtered (.bound args) q (src pos)).map (q.rowOutput (.bound args)))) := by
  simp only [selectPlan, Plan.run, ScanOutput.run, Filter.rows_eq, List.map_map]
  have accepts : (Filter.whereClause args false q.filter).accepts [] = Resolved.conditionKeeps q.filter (.bound args) := by
    funext r
    simp [Filter.accepts_where]
  rw [accepts]
  congr 2
  apply List.map_congr_left
  intro row _
  apply List.map_congr_left
  intro col _
  cases col <;> simp [compileColumn, CompiledExpr.run_compile, Resolved.Expr.eval]

/-- A simple, calm SELECT returns the plan output from every matching context. Proof sketch:
resolve on the shared catalog, apply the unordered execution rule, and transport the filter
and projection through the input scan permutation. -/
private theorem selectStep {catalog : Database} {stmt : Syntax.Statement} {args : List Value}
    {q : Resolved.Query} {pos : Nat} {shape : CatalogTable} {after : ResolveState}
    (select : stmt.asQuery?.isSome = true)
    (resolved : resolveStatement runContext (catalog.raw.connection {}).resolveState stmt = .ok (.query q [], after))
    (simple : q = Resolved.Query.simple [.first pos] q.filter q.columns q.names)
    (calm : (Resolved.Statement.query q []).Calm) (located : catalog.raw.catalog.tableAt pos = some shape) :
    Checked (selectPlan pos q args) ⟨[(stmt, args)]⟩ catalog := by
  intro start src input
  obtain ⟨present, original⟩ := input.table located
  let ctx := Resolved.EvalContext.bound args
  have perm := (original.filter (fun r => q.filter.all (fun e => Resolved.truthy (e.eval ctx r)))).map (q.rowOutput ctx)
  have output : (runScriptStep runContext start.clock start.index start.connection stmt args).output =
      (selectPlan pos q args).run src := by
    rw [← input.names] at resolved
    rw [runScriptStep_output_of_resolved resolved]
    obtain ⟨filter, columns, names, rfl⟩ :
        ∃ f cs ns, q = Resolved.Query.simple [.first pos] f cs ns := ⟨_, _, _, simple⟩
    rw [resolvedStepOutput_calm_unordered _ _ _ _ calm rfl rfl rfl rfl rfl rfl
      (Resolved.Query.source_first _ _ _ _ _ rfl present) (by intro impossible; cases impossible)
      (by simp [Resolved.Query.fails, Resolved.Query.simple]) rfl,
      Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
    rw [selectPlan_eq]
    exact congrArg Output.rows ((Resolved.normalForm_eq_iff_perm _ _).mpr perm)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, form⟩ := Syntax.Statement.select_of_asQuery select
  apply Sql.check_send_select form
  · cases step : runScriptStep runContext start.clock start.index start.connection stmt args with
    | ended => rw [step] at output; cases output
    | continued => exact ⟨_, _, _, rfl⟩
  · intro selected choice
    rw [output] at choice
    obtain rfl | impossible := choice
    · simp [ExecutionContext.next]
    · exact impossible.elim

/-- Resolve each statement on the catalog. Compose a plain DELETE with the remaining plan,
or return its affected-row count when it is the final statement. -/
private def compileSteps? (catalog : Database) : (stmts : List (Syntax.Statement × List Value)) →
    Option { p : Plan // Checked p ⟨stmts⟩ catalog }
  | [] => none
  | (stmt, args) :: rest => do
    match h : resolveStatement runContext (catalog.raw.connection {}).resolveState stmt with
    | .ok (.delete pos filter [] [] none, _) =>
      match located : catalog.raw.catalog.tableAt pos with
      | some _ =>
        if calm : (Resolved.Statement.delete pos filter [] [] none).Calm then
          have step {s src} (i : Inputs catalog s src) := deleteStep args h located calm i
          match tailEq : rest with
          | [] => return ⟨⟨pos, Filter.whereClause args false filter, .count⟩,
              by
                subst rest
                intro s src input
                apply Sql.check_mono (step input)
                intro _ _ result
                simpa only [Plan.run, ScanOutput.run, Filter.rows_eq, selectedBy] using result.1⟩
          | second :: tail =>
            let next ← compileSteps? catalog rest
            return ⟨next.val.prependDelete pos filter args, by
              subst rest
              intro s src input
              apply (check_send_append ⟨[(stmt, args)]⟩ ⟨second :: tail⟩ _ s).2
              rw [Plan.run_prependDelete]
              exact Sql.check_mono (step input) (fun _ _ result => next.property _ _ result.2)⟩
        else none
      | none => none
    | .ok (.query q [], _) =>
      if tailEq : rest = [] then
        let [.first pos] := q.sources | none
        match located : catalog.raw.catalog.tableAt pos with
        | some _ =>
          if ready : stmt.asQuery?.isSome = true ∧
              q = Resolved.Query.simple [.first pos] q.filter q.columns q.names ∧ (Resolved.Statement.query q []).Calm then
            return ⟨selectPlan pos q args, by subst rest; exact selectStep ready.1 h ready.2.1 ready.2.2 located⟩
          else none
        | none => none
      else none
    | _ => none

/-- The certified scan data for a script. This form supports structural plan comparisons. -/
def Script.compileScan? (s : Script) (catalog : Database) : Option {p : Plan // Checked p s catalog} := do
  let plan ← compileSteps? catalog s.statements
  return ⟨plan.val.pruneEmpty, fun state src input => by
    simpa only [Plan.run_pruneEmpty] using plan.property state src input⟩

/-- For two plans checked for their scripts on one catalog, equal plan data give
{name}`Script.SameLastOn` on that catalog. Proof sketch: the compiler certificates give
the two outputs, then the data equality identifies their evaluations. -/
theorem CompiledScript.same_of_eq {p q : Plan} {a b : Script} {catalog : Database}
    (left : Checked p a catalog) (right : Checked q b catalog) (same : p = q) : a.SameLastOn b catalog := by
  subst q
  exact (LastOutputPlan.sameLastOn_iff (correct left) (correct right)).mpr (fun _ _ _ _ => rfl)

/-- Compile a sequence of plain DELETEs with an optional final single-table SELECT,
or one SELECT. Each plan carries its last-output certificate for the supplied catalog. -/
def Script.compileLastOutput? (s : Script) (catalog : Database) :
    Option { p : LastOutputPlan // p.Correct s catalog } := do
  let plan ← s.compileScan? catalog
  return ⟨asLast plan.val, correct plan.property⟩

end Belay.Sqlite
