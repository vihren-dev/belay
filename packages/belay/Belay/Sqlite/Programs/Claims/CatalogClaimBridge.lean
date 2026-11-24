import Belay.Sqlite.Programs.Claims.ResolvedOutputBridge

set_option doc.verso true

/-! The bridge laws of a query assertion at a context whose database has a known catalog. The resolution of the
statement on a database reads only the catalog of the database, so the kernel can compute it on a fixed schema with
the same catalog. The laws here take that computed resolution as a premise and give the output of the resolved
statement at the default observation of the context. The tactic {lit}`sql_holds` applies them. -/

namespace Belay.Sqlite
open Model

/-- For every result of a computation that can fail, whose value is a pair, and every first part: if the first part
of the value is the given one, the result is that first part with some second part. Proof sketch: an error maps to
an error, so the result is a value; its first part is the given one. -/
theorem Except.exists_of_map_fst {ε α β : Type} {result : Except ε (α × β)} {first : α}
    (mapped : result.map Prod.fst = .ok first) : ∃ second, result = .ok (first, second) := by
  cases result with
  | error _ => simp [Except.map] at mapped
  | ok pair =>
    simp only [Except.map, Except.ok.injEq] at mapped
    exact ⟨pair.2, by rw [← mapped]⟩

/-- For every two raw databases with the same catalog and all counters, the resolution state of the connection of the
first with the counters is that of the connection of the second with no counters. Proof sketch: the state reads only
the catalog. -/
theorem Database.Raw.resolveState_of_catalog {raw schema : Database.Raw} (same : raw.catalog = schema.catalog)
    (counters : Counters) : (raw.connection counters).resolveState = (schema.connection {}).resolveState := by
  simp only [Connection.resolveState, Database.Raw.connection, same]

/-- For every two raw databases with the same catalog and every position that has a table in that catalog: the
first database has at the position the table of the catalog entry with the rows that it stores at the position.
Proof sketch: {name}`Model.Database.table` maps the entry of the catalog. -/
theorem Database.Raw.table_of_catalog {raw schema : Database.Raw} (same : raw.catalog = schema.catalog)
    (position : Nat) (present : (schema.catalog.tableAt position).isSome = true) :
    raw.table position =
      some { shape := (schema.catalog.tableAt position).get present, rows := raw.rows.getD position [] } := by
  unfold Model.Database.table
  rw [same]
  conv => lhs; rw [← Option.some_get present]
  rfl

/-- For every script of exactly one read-only statement with values, every context and every raw database
{lit}`schema` with the catalog of the context's database: if the statement resolves on the catalog of
{lit}`schema` to {lit}`resolved`, the default assertion {name}`Holds.reached` holds exactly when the output of
{lit}`resolved` at the idle connection of the context's database, without a clock, at index zero and without an
initial database, has rows ({name}`Output.hasRows`). Proof sketch: the resolution state reads only the catalog
({name}`Database.Raw.resolveState_of_catalog`), so {name}`Holds.inContext_iff_hasRows` applies at the default
observation. -/
theorem Holds.reached_iff_of_catalog {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (context : ExecutionContext) {schema : Database.Raw} {resolved : Resolved.Statement}
    (isQuery : script.isQuery = true) (single : script.statements = [(statement, parameters)])
    (same : context.connection.state.database.catalog = schema.catalog)
    (resolves : (resolveStatement runContext (schema.connection {}).resolveState statement).map Prod.fst =
      .ok resolved) :
    Holds.reached script context isQuery ↔
      (resolvedStepOutput none 0 (Database.Raw.connection context.connection.state.database {}) parameters
        resolved).hasRows = true := by
  obtain ⟨_, found⟩ := Except.exists_of_map_fst resolves
  exact Holds.inContext_iff_hasRows _ isQuery single (by
    show resolveStatement runContext
      (Database.Raw.connection context.connection.state.database {}).resolveState statement = _
    rw [Database.Raw.resolveState_of_catalog same]
    exact found)

/-- For every script of exactly one {lit}`SELECT` with values, its query and subqueries
({name}`Syntax.Statement.asQuery?`), every initial database, every context, and two raw databases
{lit}`initialSchema` and {lit}`schema` with the catalog of the initial database and of the context's database: if the
query resolves on these two catalogs ({name}`resolveTwoState`) to {lit}`resolved`, the default two-state assertion
{name}`Holds.reachedSince` holds exactly when the output of {lit}`resolved` at the idle connection of the context's
database, without a clock and at index zero, has rows ({name}`Output.hasRows`). The output receives
{lit}`chosen`, the initial database when the query or one of its subqueries has a source with a schema name
({name}`usesSchema`), else no database. Proof sketch: rewrite the two catalogs and apply
{name}`Holds.inContextSince_iff_hasRows` at the default observation. -/
theorem Holds.reachedSince_iff_of_catalog {script : Script} {statement : Syntax.Statement}
    {parameters : List Value} {query : Syntax.Subquery} {subqueries : List Syntax.Subquery} (initial : Database)
    (context : ExecutionContext) {initialSchema schema : Database.Raw} {resolved : Resolved.Statement}
    {chosen : Option Database.Raw}
    (isQuery : script.isQuery = true) (single : script.statements = [(statement, parameters)])
    (parts : statement.asQuery? = some (query, subqueries))
    (initialSame : initial.raw.catalog = initialSchema.catalog)
    (same : context.connection.state.database.catalog = schema.catalog)
    (resolves : (resolveTwoState runContext initialSchema.catalog schema.catalog query subqueries).map Prod.fst =
      .ok resolved)
    (choice : (if usesSchema query subqueries then some initial.raw else none) = chosen) :
    Holds.reachedSince script initial context isQuery ↔
      (resolvedStepOutput none 0 (Database.Raw.connection context.connection.state.database {}) parameters resolved
        chosen).hasRows = true := by
  obtain ⟨_, found⟩ := Except.exists_of_map_fst resolves
  subst choice
  exact Holds.inContextSince_iff_hasRows initial _ isQuery single parts (by
    show resolveTwoState runContext initial.raw.catalog context.connection.state.database.catalog query subqueries = _
    rw [initialSame, same]
    exact found)

end Belay.Sqlite
