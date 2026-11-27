import Belay.Sqlite.Programs.Claims.LastOutput
import Belay.Sqlite.Programs.Claims.ReadStepRule
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution
import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Programs.Claims.CompiledExpr

set_option doc.verso true

namespace Belay.Sqlite
open Model hiding Database

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

/-- Compile a WHERE to a restriction on the input rows. A constant false or NULL condition
rejects all rows immediately. An absent condition accepts the full scan. -/
private def compileWhere (args : List Value) : Option Resolved.Expr → (Unit → List (List Value)) → List (List Value)
  | none => fun source => source ()
  | some e => match CompiledExpr.compile args e with
    | .constant result => if Resolved.truthy result.1 then (fun source => source ()) else fun _ => []
    | .perRow f => fun source => (source ()).filter fun row => Resolved.truthy (f row).1

/-- Compile each projection before visiting rows. Scalar expressions reuse their bound
values, and aggregate outputs retain the model's single-row interpretation. -/
private def compileColumn (args : List Value) : Resolved.Output → List Value → Value
  | .scalar e => let plan := CompiledExpr.compile args e; fun row => (plan.run row).1
  | .aggregate a => fun row => a.eval (.bound args) [row]

/-- The compiled WHERE selects exactly the model's filtered rows on every input.
Proof sketch: use expression correctness, then simplify filtering by a constant decision. -/
private theorem compileWhere_eq (args : List Value) (q : Resolved.Query) (xs : List (List Value)) :
    compileWhere args q.filter (fun _ => xs) = Resolved.filtered (.bound args) q xs := by
  unfold Resolved.filtered
  cases h : q.filter with
  | none => exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  | some e =>
    simp only [Option.all_some]
    have same := List.filter_congr (l := xs) (fun r _ =>
      congrArg (fun result => Resolved.truthy result.1) (CompiledExpr.run_compile args e r))
    apply Eq.trans _ same
    cases plan : CompiledExpr.compile args e with
    | constant result =>
      cases keep : Resolved.truthy result.1 <;> simp only [compileWhere, plan, CompiledExpr.run, keep,
        Bool.false_eq_true, ite_false, ite_true]
      · exact (List.filter_eq_nil_iff.mpr (fun _ _ => by decide)).symm
      · exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
    | perRow f => simp [compileWhere, plan, CompiledExpr.run]

/-- The last-output plan for a plain SELECT. Compile the WHERE and projection expressions
with their bindings before reading the database. The result records every duplicate. -/
def LastOutputPlan.scan (pos : Nat) (q : Resolved.Query) (args : List Value) : LastOutputPlan :=
  let restrict := compileWhere args q.filter
  let columns := q.columns.map (compileColumn args)
  fun db _ => rowBag ((restrict (fun _ => db.scanAt pos)).map fun row => columns.map (fun f => f row))

/-- A closed WHERE that evaluates to false or NULL gives an empty result on every database.
Proof sketch: inspect the compiled condition. Only a rejecting constant meets the premise. -/
theorem LastOutputPlan.scan_eq_empty (pos : Nat) (q : Resolved.Query) (args : List Value)
    (rejects : q.filter.any (fun e => (CompiledExpr.compile args e).rejectsAll)) (db : Database) (env : Env) :
    scan pos q args db env = rowBag [] := by
  cases h : q.filter with
  | none => simp [h] at rejects
  | some e =>
    cases plan : CompiledExpr.compile args e with
    | perRow f => simp [h, plan, CompiledExpr.rejectsAll] at rejects
    | constant result =>
      simp [h, plan, CompiledExpr.rejectsAll] at rejects
      simp [scan, h, compileWhere, plan, rejects]

/-- On every input the compiled scan gives the normalized bag of the model's projected
rows. Proof sketch: rewrite the filter and each compiled scalar with their evaluation laws. -/
private theorem scan_eq (pos : Nat) (q : Resolved.Query) (args : List Value) (db : Database) (env : Env) :
    LastOutputPlan.scan pos q args db env = LastOutputPlan.rowBag
      ((Resolved.filtered (.bound args) q (db.scanAt pos)).map (q.rowOutput (.bound args))) := by
  unfold LastOutputPlan.scan
  simp only [compileWhere_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro row _
  apply List.map_congr_left
  intro col _
  cases col <;> simp [compileColumn, CompiledExpr.run_compile, Resolved.Expr.eval]

/-- A calm singleton SELECT whose resolution is a plain scan with a known table has
exactly the scan plan's last output on every admitted start. Proof sketch: transport
resolution across the common catalog, apply the unordered SELECT rule, then lift the
step's rows to every branch of the singleton send. -/
private theorem scan_correct {catalog : Database} {stmt : Syntax.Statement} {args : List Value}
    {q : Resolved.Query} {pos : Nat} {shape : CatalogTable} {after : ResolveState}
    (select : stmt.asQuery?.isSome = true)
    (resolved : resolveStatement runContext (catalog.raw.connection {}).resolveState stmt = .ok (.query q [], after))
    (simple : q = Resolved.Query.simple [.first pos] q.filter q.columns q.names)
    (calm : (Resolved.Statement.query q []).Calm) (located : catalog.raw.catalog.tableAt pos = some shape) :
    (LastOutputPlan.scan pos q args).Correct ⟨[(stmt, args)]⟩ catalog := by
  intro db schema env _
  let start := ExecutionContext.initial db env
  obtain ⟨present, scanned⟩ := Database.table_of_catalog schema located
  let ctx := Resolved.EvalContext.bound args
  let rows := (Resolved.filtered ctx q (db.scanAt pos)).map (q.rowOutput ctx)
  have output : (runScriptStep runContext start.clock start.index start.connection stmt args).output =
      .rows (Resolved.normalForm rows) := by
    have same := select_resolution_of_same_catalog runContext stmt select start.connection.resolveState
      (catalog.raw.connection {}).resolveState schema
    rw [resolved] at same
    cases h : resolveStatement runContext start.connection.resolveState stmt with
    | error e => simp [h, Except.map] at same
    | ok pair =>
      rcases pair with ⟨st, next⟩
      simp [h, Except.map] at same
      subst st
      obtain ⟨filter, columns, names, rfl⟩ :
          ∃ f cs ns, q = Resolved.Query.simple [.first pos] f cs ns := ⟨_, _, _, simple⟩
      rw [runScriptStep_output_of_resolved h, resolvedStepOutput_calm_unordered _ _ _ _ calm
        rfl rfl rfl rfl rfl rfl (Resolved.Query.source_first _ _ _ _ _ rfl present)
        (by intro impossible; cases impossible) (by simp [Resolved.Query.fails, Resolved.Query.simple]) rfl,
        Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
      simp only [rows, ctx, scanned]
  rw [scan_eq]
  apply Script.lastOutputProfile_of_check
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, form⟩ := Syntax.Statement.select_of_asQuery select
  apply Sql.check_send_select form
  · cases step : runScriptStep runContext start.clock start.index start.connection stmt args with
    | ended => rw [step] at output; cases output
    | continued => exact ⟨_, _, _, rfl⟩
  · intro selected choice
    rw [output] at choice
    obtain rfl | impossible := choice
    · rfl
    · exact impossible.elim

/-- Compile a singleton, calm, unordered SELECT over one table with its bound values. On
success return the plan with a proof of {name}`LastOutputPlan.Correct`. For example, a
single-table projection with a column comparison in WHERE can compile. Unsupported scripts
and failed resolutions return no plan. -/
def Script.compileLastOutput? (s : Script) (catalog : Database) :
    Option { p : LastOutputPlan // p.Correct s catalog } :=
  match s with
  | ⟨[(stmt, args)]⟩ => do
    match resolved : resolveStatement runContext (catalog.raw.connection {}).resolveState stmt with
    | .ok (.query q [], _) =>
      let [.first pos] := q.sources | none
      match located : catalog.raw.catalog.tableAt pos with
      | some _ =>
        if ready : stmt.asQuery?.isSome = true ∧
            q = Resolved.Query.simple [.first pos] q.filter q.columns q.names ∧ (Resolved.Statement.query q []).Calm then
          return ⟨LastOutputPlan.scan pos q args, scan_correct ready.1 resolved ready.2.1 ready.2.2 located⟩
        else none
      | none => none
    | _ => none
  | _ => none

end Belay.Sqlite
