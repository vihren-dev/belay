import Belay.Sqlite.Model.TwoStateStatementLaws

set_option doc.verso true

/-! The observation of a read-only query over two fixed databases (ADR 0017, S6): the current
database of a connection and the initial database, which the query names with the schema
{lit}`before`, as in {lit}`SELECT t.a FROM before.t`. The initial database is an argument of the
observation and is never changed by it; the connection is the one that the modeled statements ran
on. The observation uses the evaluator and the resolver of {lit}`runScriptStep`
with the optional initial database and catalog that they take; it has no copy of them.

* {lit}`Syntax.Statement.asQuery?` reads the query out of a {lit}`SELECT`.
* {lit}`resolveTwoState` resolves it against both catalogs.
* {lit}`observeTwoState` gives its output.
* {lit}`observeTwoState_ordinary` shows that a query without a schema name
  has the output of {lit}`runScriptStep`.
* {lit}`observeTwoState_initial_irrelevant` shows that a query that does not
  read the initial origin does not depend on the initial database. -/

namespace Belay.Sqlite.Model

/-- The query and the list of subqueries of a {lit}`SELECT` statement, as
{name}`resolveStatement` gives them to the resolver; none for every other statement. -/
def Syntax.Statement.asQuery? : Syntax.Statement → Option (Syntax.Subquery × List Syntax.Subquery)
  | .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound =>
    some ({ columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct, compound },
      subqueries)
  | _ => none

/-- Whether a query and its subqueries, which hold every derived table, expression subquery, common
table and compound term of the statement, name a schema anywhere. Only such a query needs the initial
database. -/
def usesSchema (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) : Bool :=
  (query :: subqueries).any Syntax.Subquery.hasSchemaSource

/-- Resolve a query against the catalog of the initial database and the catalog of the current database.
A query with no schema name resolves as {name}`resolveSelect` does without an initial catalog, so that
the initial catalog cannot change it ({lit}`resolveTwoState_ordinary`); a query with a schema name
resolves its sources of {lit}`before` in the initial catalog and all others in the current catalog.
A schema name other than {lit}`before` is the restriction {name}`RestrictionKind.initialDatabase`. -/
def resolveTwoState (context : ResolveContext) (initial current : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) : StatementResolution :=
  if usesSchema query subqueries then resolveSelect context current query subqueries (some initial)
  else resolveSelect context current query subqueries

/-- The output of a read-only query over the fixed initial database and the database of a connection,
with the values bound to its parameters, at the clock value of an index and with the counters of the
connection. A restriction of the resolver is {name}`Output.unmodeled`. A table that the initial database
lacks, or a query that the model does not describe, is {name}`Output.unmodeled` too, never an empty
result. The query reads the initial database only through sources with a schema name, so a
query without a schema name does not read it. -/
def observeTwoState (context : ResolveContext) (clock : Option Clock) (index : Nat) (initial : Database)
    (connection : Connection) (parameters : List Value) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) : Output :=
  match resolveTwoState context initial.catalog connection.state.database.catalog query subqueries with
  | .error restriction => .unmodeled restriction.reason
  | .ok (resolved, _) =>
    resolvedStepOutput clock index connection parameters resolved (if usesSchema query subqueries then some initial else none)

/-- For every context, catalogs and query without a schema name, {name}`resolveTwoState` is
{name}`resolveSelect` without an initial catalog, whatever the initial catalog is. -/
theorem resolveTwoState_ordinary (context : ResolveContext) (initial current : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (plain : usesSchema query subqueries = false) :
    resolveTwoState context initial current query subqueries = resolveSelect context current query subqueries := by
  simp [resolveTwoState, plain]

/-- For every context, clock, index, initial database, connection, values and {lit}`SELECT` statement
whose query has no schema name, the observation is the output of the ordinary step of the statement
({name}`runScriptStep`). In plain words: the two-state observation extends the ordinary run
conservatively; without a schema name it gives the same output, including every restriction and every
failure, and it does not read the initial database. Proof sketch: {name}`runScriptStep_output` gives the output of the step
as the output of the resolved statement; the select case of {name}`resolveStatement` is
{name}`resolveSelect`, which is {name}`resolveTwoState` by {name}`resolveTwoState_ordinary`, and
the observation then passes {lit}`none` as the initial database, as the step does. -/
theorem observeTwoState_ordinary (context : ResolveContext) (clock : Option Clock) (index : Nat) (initial : Database)
    (connection : Connection) (parameters : List Value) (statement : Syntax.Statement)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery)
    (found : statement.asQuery? = some (query, subqueries)) (plain : usesSchema query subqueries = false) :
    observeTwoState context clock index initial connection parameters query subqueries =
      (runScriptStep context clock index connection statement parameters).output := by
  cases statement <;> simp only [Syntax.Statement.asQuery?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at found
  case select columns source joins filter groupBy orderBy limit offset subs having distinct compound =>
    obtain ⟨rfl, rfl⟩ := found
    rw [runScriptStep_output]
    simp only [observeTwoState, resolveTwoState_ordinary _ _ _ _ _ plain, resolveStatement, ResolveState.withCatalog,
      Connection.resolveState, plain]
    cases resolveSelect context connection.state.database.catalog _ _ <;> rfl

/-- For every context, clock, index, two initial databases, connection, values and query without a schema name,
the observation is the same for both initial databases. In plain words: a query that names no schema is
independent of the initial database that is supplied, also of its catalog. Proof sketch: the resolution is
{name}`resolveSelect` for both ({name}`resolveTwoState_ordinary`) and the observation passes none. -/
theorem observeTwoState_unqualified_irrelevant (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (first second : Database) (connection : Connection) (parameters : List Value) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (plain : usesSchema query subqueries = false) :
    observeTwoState context clock index first connection parameters query subqueries =
      observeTwoState context clock index second connection parameters query subqueries := by
  simp [observeTwoState, resolveTwoState_ordinary _ _ _ _ _ plain, plain]

/-- For every context, clock, index, two initial databases with the same catalog, connection, values, query
and subqueries, if the resolution with the first one gives a resolved statement that has no source in the
initial database, then the observation is the same for both initial databases. In plain words: when the query
does not read the initial origin, for example because its only schema name is in a common table that the query
does not use, the rows of the initial database cannot change the output; the catalogs must agree, because the
catalog decides the resolution. Proof sketch: the resolution is the same for both catalogs, and
{name}`resolvedStepOutput_initial_irrelevant` shows that the output does not read the rows. -/
theorem observeTwoState_initial_irrelevant (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (first second : Database) (connection : Connection) (parameters : List Value) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (resolved : Resolved.Statement) (catalog : Catalog)
    (same : first.catalog = second.catalog)
    (found : resolveTwoState context first.catalog connection.state.database.catalog query subqueries =
      .ok (resolved, catalog))
    (plain : resolved.readsInitial = false) :
    observeTwoState context clock index first connection parameters query subqueries =
      observeTwoState context clock index second connection parameters query subqueries := by
  unfold observeTwoState
  rw [← same, found]
  dsimp only
  cases uses : usesSchema query subqueries
  · simp
  · simp only [ite_true]
    exact resolvedStepOutput_initial_irrelevant clock index connection parameters resolved (some first) (some second) plain

end Belay.Sqlite.Model
