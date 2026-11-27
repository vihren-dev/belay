import Belay.Sqlite.Programs.Claims.CompiledScript
import Belay.Sqlite.Model.Programs.Scripts.PlainDeleteCoverage
import Belay.Sqlite.Model.Programs.Scripts.StatementCalm
import Belay.Sqlite.Model.Schema.Columns.TwoStateKeptRows

set_option doc.verso true

/-! Fuse a plain DELETE into the following scan and certify its step for the script compiler. -/

namespace Belay.Sqlite.CompiledScript
open Model hiding Database

/-- Give the next statement the surviving rows of the target table and the original scans of other tables. -/
def afterDelete (src : Sources) (pos : Nat) (selectedBy : List Value → Bool) : Sources :=
  fun n => if n = pos then (src pos).filter (fun r => !selectedBy r) else src n

/-- Compile the DELETE predicate with its own bindings. An absent WHERE selects every row. -/
def selectedBy (p : Option Resolved.Expr) (args : List Value) : List Value → Bool :=
  (Filter.whereClause args false p).accepts []

/-- The DELETE selects precisely the rows accepted by its compiled filter.
Proof sketch: specialize the filter correctness law to a positive WHERE. -/
theorem selectedBy_eq (p : Option Resolved.Expr) (args row : List Value) :
    selectedBy p args row = Resolved.conditionKeeps p (.bound args) row := by
  simp [selectedBy, Filter.accepts_where]

/-- Fuse a preceding DELETE into the scan at compilation time. -/
def Plan.prependDelete (next : Plan) (pos : Nat) (p : Option Resolved.Expr) (args : List Value) : Plan :=
  if next.pos = pos then { next with filter := (Filter.whereClause args true p).both next.filter } else next

/-- A fused scan reads exactly the surviving rows. Proof sketch: the two independent
acceptance conditions are the conjunction of the original filters. -/
theorem Plan.run_prependDelete (next : Plan) (pos : Nat) (p : Option Resolved.Expr) (args : List Value)
    (src : Sources) : (next.prependDelete pos p args).run src = next.run (afterDelete src pos (selectedBy p args)) := by
  by_cases same : next.pos = pos
  · simp only [prependDelete, same, ite_true, run, Filter.rows_eq, afterDelete, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro r _
    simp [Filter.accepts_both, Filter.accepts_where, selectedBy_eq, Bool.and_comm]
  · simp [prependDelete, same, run, afterDelete]

/-- A plain, calm DELETE reports the number of matching rows and establishes the inputs for the
next statement. Proof sketch: use the exact DELETE step and its fault-free filter, then apply
the scan law for the changed table and preserve the scans of every other table. -/
theorem deleteStep {catalog : Database} {stmt : Syntax.Statement} {p : Option Resolved.Expr}
    {pos : Nat} {shape : CatalogTable} {after : ResolveState} (args : List Value)
    (resolved : resolveStatement runContext (catalog.raw.connection {}).resolveState stmt =
      .ok (.delete pos p [] [] none, after))
    (located : catalog.raw.catalog.tableAt pos = some shape)
    (calm : (Resolved.Statement.delete pos p [] [] none).Calm)
    {s src} (input : Inputs catalog s src) :
    (send ⟨[(stmt, args)]⟩).check (fun _ next =>
      next.outputs.getLast? = some (.done ((src pos).filter (selectedBy p args)).length) ∧
      Inputs catalog next (afterDelete src pos (selectedBy p args))) s := by
  let db := s.connection.state.database
  let t : Table := ⟨shape, db.rows.getD pos []⟩
  have cat : db.catalog = catalog.raw.catalog := congrArg ResolveState.catalog input.names
  obtain ⟨present, original⟩ := input.table located
  change db.table pos = some t at present
  change (Resolved.sourceRows t).Perm (src pos) at original
  have aligned : pos < db.rows.length := by
    rw [input.valid.1.admitted.rowsShaped.1, cat]
    apply Nat.lt_of_not_ge
    intro outside
    simp [Catalog.tableAt, List.getElem?_eq_none outside] at located
  have found := resolved
  rw [← input.names] at found
  let ctx := Resolved.EvalContext.bound args
  have ready : deleteJsonReady ctx t p [] = true := by
    apply PlainDeleteCoverage.ready_of_rows
    intro row _
    apply List.any_eq_false.mpr
    intro e mem
    have safe := (calm e (by simpa [Resolved.Statement.clockExpressions, Resolved.WriteRules.expressions] using mem)).1
    have quiet : ctx.Quiet := fun _ _ => ⟨rfl, rfl, rfl⟩
    unfold Resolved.Expr.mayFailOn
    rw [Resolved.Expr.fault_of_plain_at _ row (quiet.at row) e safe]
    decide
  have step := runScriptStep_plainDelete_eq (clock := s.clock) (index := s.index) (parameters := args) found
  simp only [PlainDeleteCoverage.timed_without_read calm.readsClock, calm.counterReads, Counters.firstUnknown_nil,
    Counters.view_nil, show s.connection.state.database.table pos = some t from present,
    Resolved.subqueriesPlain, List.all_nil, Bool.true_and,
    show Resolved.statementContext 0 {} args s.connection.state.database [] = ctx from rfl, ready, ite_true] at step
  apply Sql.check_send_of_rule step input.valid rfl
  apply Sql.sendReached_single (by intros; simp)
  intro valid
  constructor
  · simp only [ExecutionContext.next, List.getLast?_append, List.getLast?_cons, Option.some_or]
    change some (Output.done _) = some (Output.done _)
    simp only [Option.some.injEq, Output.done.injEq]
    have count := (original.filter (selectedBy p args)).length_eq
    have selects : LiteralData.selected ctx p = fun row => selectedBy p args row.values := by
      funext row
      exact (selectedBy_eq p args row.values).symm
    rw [selects]
    simpa only [Resolved.sourceRows, List.filter_map, List.length_map, Function.comp_def] using count
  · refine ⟨input.names, valid, ?_⟩
    intro n
    change (scans (db.setRows pos (LiteralData.deleted ctx t p).rows) n).Perm _
    by_cases h : n = pos
    · subst n
      have effect := (Resolved.sourceRows_deleted t ctx p).trans
        (original.filter (fun row => !Resolved.conditionKeeps p ctx row))
      simpa [scans, Model.Database.table_setRows _ present aligned, afterDelete, selectedBy_eq,
        LiteralData.deleted, t, ctx] using effect
    · simpa [scans, Model.Database.table_setRows_other _ _ h, afterDelete, h, db] using input.agree n

end Belay.Sqlite.CompiledScript
