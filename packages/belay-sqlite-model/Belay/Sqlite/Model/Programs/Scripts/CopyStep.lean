import Belay.Sqlite.Model.Schema.Writes.CopyRun
import Belay.Sqlite.Model.Programs.Scripts.InsertSelectStepLaws
import Belay.Sqlite.Model.Programs.Scripts.InsertSelectAlternatives

set_option doc.verso true

/-! A script step that copies rows from one table to another, including the
connections and outputs for alternative scans. -/

namespace Belay.Sqlite.Model

/-- Consider any script step on a connection with valid current and saved databases for the
resolution profile. Its source and empty target must be present at the given positions.
The source must have a rowid alias, its definition and the target keys must pass
{name}`CatalogTable.copyCompatible` for the target definition, and every source row must
satisfy {name}`LiteralData.typesFit` for that definition. If the statement resolves to a
full-column INSERT from {name}`Resolved.Query.copyOf` as specified, with no conflict clauses,
RETURNING, subqueries or write rules, then:
* the step continues;
* its output is successful and its next database differs only at the target, which holds
  exactly the source rows in {name}`Table.scanRows` order;
* when there is one source access order, there are no further executions;
* every further execution has a successful output and the same database except for the
  target rows, which are a permutation of the source rows, including their rowids.
The clock, script index, bound parameters, result names and post-resolution state are arbitrary.
Proof sketch: reading column values needs neither clock nor counters. {name}`runStatement_copyOf`
gives the effect of each scan. Readiness gives the executions, and each successful INSERT
effect becomes a successful output and an updated connection. -/
theorem runScriptStep_copyOf {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {s t : Nat} {source target : Table} (names : List String) {aliasPos : Nat}
    (src : c.state.database.table s = some source) (dst : c.state.database.table t = some target)
    (compatible : source.shape.copyCompatible target.shape (c.state.database.keys t target) = true)
    (alias : source.shape.rowidAlias = some aliasPos) (empty : target.rows = [])
    (valid : c.state.Holds (Database.Valid context.profile))
    (typed : ∀ row ∈ source.rows, LiteralData.typesFit target.shape row = true) :
    let cells := (List.range target.shape.columns.length).map Resolved.SourceCell.source
    let query := Resolved.Query.copyOf s source.shape.columns.length names
    let stmt := Resolved.Statement.insertSelect t cells query [] [] none [] none
    resolveStatement context c.resolveState statement = .ok (stmt, after) →
    ∃ output next others, runScriptStep context clock index c statement parameters = .continued output next others ∧
      output.isError = false ∧ next.state.database = c.state.database.setRows t source.scanRows ∧
      (Table.accessOrders c.state.database.catalog s source = [source.scanRows] → others = []) ∧
      ∀ ex ∈ others, ex.output.isError = false ∧
        ∃ rows, rows.Perm source.rows ∧ ex.next.state.database = c.state.database.setRows t rows := by
  intro cells query stmt resolved
  let value : Int := 0
  have columns (p : Resolved.Expr → Bool) (noRead : ∀ i, p (.column i) = false) :
      stmt.clockExpressions.any p = false := by
    simp [stmt, cells, query, Resolved.Statement.clockExpressions, List.filterMap_map,
      Resolved.SourceCell.expression?, Resolved.WriteRules.expressions, Resolved.Query.copyOf, Resolved.Query.simple,
      Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.QuerySource.first,
      Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands, Function.comp_def,
      List.any_eq_false, noRead]
  have timed : statementClock clock index stmt = some value := by
    rw [statementClock, Resolved.Statement.readsClock, columns _ (fun _ => rfl)]
    rfl
  have reads : stmt.counterReads = [] := by
    have noCounter (kind : CounterKind) := columns (fun x => x.any (Resolved.Expr.readsCounterHere kind)) (fun _ => rfl)
    simp [Resolved.Statement.counterReads, noCounter]
  have known : c.state.counters.firstUnknown stmt.counterReads = none := by rw [reads]; rfl
  let run := c.state.statementRun value parameters stmt
  obtain ⟨runReady, effect, unique, also⟩ := runStatement_copyOf value (c.state.counters.view stmt.counterReads)
    parameters c.state.database s t source target names src dst compatible alias empty
    (valid.1.admitted.table src) (valid.1.notNull s source src) typed
  have ready : run.ready = true := by
    change (_ && _) = true
    rw [Bool.and_eq_true]
    exact ⟨runReady, by rw [known]; rfl⟩
  have ok (r : StatementRun) (db : Database) (ok : r.effect = .ok db) :
      let tr := advanceRun index stmt c.state r
      Output.ofStep value parameters stmt c.state r tr = .done (r.counts.changes.getD 0) ∧
        (c.afterStep after r.counts tr).state.database = db := by
    dsimp only
    rw [advanceRun_ordinary _ _ _ _ (by rfl), ok]
    constructor <;> rfl
  obtain ⟨further, listed⟩ := StatementExecution.ofAlternatives_ok_of_ready index parameters c stmt after value ready
  have main := ok run _ effect
  have step : runScriptStep context clock index c statement parameters =
      .continued (.done (run.counts.changes.getD 0)) (c.afterStep after run.counts (advanceRun index stmt c.state run))
        (further.map StatementExecution.Traced.execution) := by
    simp only [runScriptStep, runScriptStepWith, resolved, timed, known, show (c.state.statementRun value parameters stmt).ready = true from ready,
      Bool.not_true, Bool.false_eq_true, ite_false, ranScriptStep]
    change (match Output.ofStep value parameters stmt c.state run (advanceRun index stmt c.state run) with
      | .unmodeled reason => RunStep.ended reason
      | output@(.rows _) | output@(.done _) | output@(.error _) | output@(.oneOf _) => _) = _
    rw [main.1]
    simp [listed, RunStep.withOthers, Except.map, run]
  refine ⟨_, _, _, step, rfl, main.2, ?_, ?_⟩
  · intro one
    have noAlt : run.alternatives = [] := unique one
    have none := StatementExecution.ofAlternatives_of_single index parameters c stmt after value noAlt
    rw [listed] at none
    rw [Except.ok.inj none]
    rfl
  · intro ex member
    obtain ⟨trace, m, rfl⟩ := List.mem_map.mp member
    obtain ⟨alt, am, _, tr, next, out⟩ := StatementExecution.ofAlternatives_mem listed trace m
    obtain ⟨rows, perm, copied⟩ := also alt am
    have altOk := ok alt.toRun _ copied
    rw [out, next, tr, altOk.1]
    exact ⟨rfl, rows, perm, altOk.2⟩

end Belay.Sqlite.Model
