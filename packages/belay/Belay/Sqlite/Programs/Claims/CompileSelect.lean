import Belay.Sqlite.Programs.Claims.LastOutput
import Belay.Sqlite.Programs.Claims.ReadStepRule
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution
import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule

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

/-- The last-output plan for a plain SELECT. Filter the scanned table with the resolved
WHERE and project each surviving row with the statement's bindings. An unordered query
returns one normalized bag, including all duplicate rows. -/
def LastOutputPlan.scan (pos : Nat) (q : Resolved.Query) (args : List Value) : LastOutputPlan := fun db _ =>
  let ctx := Resolved.EvalContext.bound args
  rowBag ((Resolved.filtered ctx q (db.scanAt pos)).map (q.rowOutput ctx))

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
