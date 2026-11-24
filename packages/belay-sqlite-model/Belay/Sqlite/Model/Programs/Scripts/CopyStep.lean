import Belay.Sqlite.Model.Schema.Writes.CopyRun
import Belay.Sqlite.Model.Programs.Scripts.PlainInsertSelectRule

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
gives the support and effect of each scan. In {name}`runScriptStep_plainInsertSelect_eq` each
successful effect installs its own database and reports its changes. -/
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
  obtain ⟨runReady, effect, unique, also⟩ := runStatement_copyOf value (c.state.counters.view stmt.counterReads)
    parameters c.state.database s t source target names src dst compatible alias empty
    (valid.1.admitted.table src) (valid.1.notNull s source src) typed
  change resolveStatement context c.resolveState statement = .ok (.insertSelect t cells query [] [] none [] none, after) at resolved
  rw [runScriptStep_plainInsertSelect_eq resolved]
  dsimp only [stmt, cells, query] at timed known ⊢
  simp only [timed, known, dst]
  let eval := Resolved.statementContext value (c.state.counters.view stmt.counterReads) parameters c.state.database []
  let produce := insertSelectOutcome value eval c.state.database t target cells [] none none ([] : List Resolved.Query).isEmpty
  change (insertSelectRun _ _ _ _ _ _ _ _ _ _ _ _).ready = true at runReady
  simp only [stmt, cells, query, runStatement, insertSelectRun, dst] at runReady effect unique also
  cases prods : query.productions eval c.state.database (!Resolved.Statement.collectsSource t query [] [] none) with
  | none => dsimp only [eval, stmt, cells, query] at prods; simp only [prods] at runReady; contradiction
  | some list =>
    cases list with
    | nil => simp only [eval, stmt, cells, query] at prods; simp only [prods] at runReady; contradiction
    | cons first others =>
      dsimp only [eval, stmt, cells, query] at prods
      simp only [prods, Option.isNone_none, Bool.true_or, Bool.and_true, ite_true, List.map_map, Function.comp_def]
        at runReady effect unique also ⊢
      rw [ite_eq_left (by exact runReady), effect]
      refine ⟨_, _, _, rfl, rfl, rfl, ?_, ?_⟩
      · intro one
        have noOther := List.map_eq_nil_iff.mp (unique one)
        simp [noOther]
      · intro ex mem
        obtain ⟨p, member, rfl⟩ := List.mem_map.mp mem
        obtain ⟨rows, perm, copied⟩ := also _ (List.mem_map_of_mem member)
        change (produce p).effect = .ok _ at copied
        dsimp only [produce, eval, stmt, cells, query] at copied
        rw [copied]
        simp only [StatementExecution.ofWriteEffect]
        exact ⟨rfl, rows, perm, rfl⟩

end Belay.Sqlite.Model
