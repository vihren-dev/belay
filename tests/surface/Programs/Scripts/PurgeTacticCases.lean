import PurgeFrameSchema

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_assertion_examples_test.py`: small cases of {lit}`sql_holds`. The first
two prove an {lit}`EXISTS` claim with a witness row about a context whose database has the catalog of
{name}`AssertionExamples.sessions`: as the first goal of a conjunction, where the tactic keeps the second goal, and as a
two-state claim with no catalog of the initial database. The other examples are claims for which the tactic has no
law, and its messages. Each message names the part of the claim that has no law. All but the last two assume the
catalog of {name}`AssertionExamples.sessions`. The last two show a missing hint and a goal that is not a claim. -/

namespace AssertionExamples
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- For every context whose database has the catalog of {name}`sessions` and stores a row in the table
{lit}`sessions`, the claim that the table has a row holds, and {lean}`True` holds. -/
theorem sessions_exists (context : ExecutionContext)
    (same : context.connection.state.database.catalog = sessions.raw.catalog)
    (stored : context.connection.state.database.rows.getD 0 [] ≠ []) :
    Holds.reached (sql r"SELECT 1 WHERE EXISTS (SELECT id FROM sessions)") context ∧ True := by
  constructor
  sql_holds [same]
  · obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ stored
    exact ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨(mem_sourceRows_iff _ _).2 ⟨row, member, rfl⟩, rfl⟩)⟩
  · trivial

/-- For every initial database and every context whose database has the catalog of {name}`sessions` and stores a
row in the table {lit}`sessions`, the two-state claim that the table has a row holds. The claim reads no table of
{lit}`before`, so the proof needs no catalog of the initial database. -/
theorem sessions_exists_since (initial : Database) (context : ExecutionContext)
    (same : context.connection.state.database.catalog = sessions.raw.catalog)
    (stored : context.connection.state.database.rows.getD 0 [] ≠ []) :
    Holds.reachedSince (sql r"SELECT 1 WHERE EXISTS (SELECT id FROM sessions)") initial context := by
  sql_holds [same]
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ stored
  exact ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨(mem_sourceRows_iff _ _).2 ⟨row, member, rfl⟩, rfl⟩)⟩

#print axioms sessions_exists
#print axioms sessions_exists_since

/--
error: sql_holds has no law for the names of the result columns in the query
  { sources := [], filter := some (Resolved.Expr.exists 0).not, aggregate := false, groupBy := [],
    columns := [Resolved.Output.scalar (Resolved.Expr.literal (Value.integer (Int.ofNat 1)))], names := ["verdict"],
    orderBy := [], offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 AS verdict WHERE NOT EXISTS (SELECT id FROM sessions)") context := by
  sql_holds [same]

/--
error: sql_holds has no law for the result column
  Resolved.Output.aggregate Resolved.Aggregate.countRows
which is not a scalar expression. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT count(*) FROM sessions)") context := by
  sql_holds [same]

/--
error: sql_holds has no law for ORDER BY in the query
  { sources := [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none }],
    filter := none, aggregate := false, groupBy := [], columns := [Resolved.Output.scalar (Resolved.Expr.column 0)],
    names := ["id"], orderBy := [{ key := Resolved.SortKey.expression (Resolved.Expr.column 2) }], offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT id FROM sessions ORDER BY expires_at)") context := by
  sql_holds [same]

/--
error: sql_holds has no law for LIMIT in the query
  { sources := [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none }],
    filter := none, aggregate := false, groupBy := [], columns := [Resolved.Output.scalar (Resolved.Expr.column 0)],
    names := ["id"], orderBy := [], offset := 0,
    limit :=
      some
        1 }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT id FROM sessions LIMIT 1)") context := by
  sql_holds [same]

/--
error: sql_holds has no law for an expression of
  [(Resolved.Expr.column 2).inList
      (Resolved.Arguments.cons (Resolved.Expr.literal (Value.integer (Int.ofNat 1)))
        (Resolved.Arguments.cons (Resolved.Expr.literal (Value.integer (Int.ofNat 2))) Resolved.Arguments.nil))
      (some Affinity.integer) Collation.binary false]
that is not made of columns, literals and parameters with comparisons, AND, OR, NOT and IS NULL. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE expires_at IN (1, 2))") context := by
  sql_holds [same]

/--
error: sql_holds has no law for a FROM clause without exactly one source in
  {
    sources :=
      [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none },
        { kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0,
          condition :=
            some
              (Resolved.Expr.compare Comparison.eq (some Affinity.numeric) (Resolved.Expr.column 0)
                (Resolved.Expr.column 3)) }],
    filter := none, aggregate := false, groupBy := [],
    columns := [Resolved.Output.scalar (Resolved.Expr.literal (Value.integer (Int.ofNat 1)))], names := ["1"],
    orderBy := [], offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions AS a JOIN sessions AS b ON a.id = b.id)")
      context := by
  sql_holds [same]

/--
error: sql_holds has no law for the condition
  Resolved.Expr.compare Comparison.eq none (Resolved.Expr.subquery 0)
    (Resolved.Expr.literal (Value.integer (Int.ofNat 0)))
which is not EXISTS or NOT EXISTS of a subquery. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE (SELECT count(*) FROM sessions) = 0") context := by
  sql_holds [same]

/--
error: sql_holds has no law for the expression
  Resolved.Expr.compare Comparison.lt none
    (Resolved.Expr.scalar Resolved.ScalarFunction.abs
      (Resolved.Arguments.cons (Resolved.Expr.column 2) Resolved.Arguments.nil))
    (Resolved.Expr.literal (Value.integer (Int.ofNat 3)))
which reads the clock or a counter, or calls a function that can fail. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE abs(expires_at) < 3)") context := by
  sql_holds [same]

/--
error: sql_holds has no law for a claim without WHERE
  { sources := [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none }],
    filter := none, aggregate := true, groupBy := [],
    columns := [Resolved.Output.aggregate Resolved.Aggregate.countRows], names := ["count(*)"], orderBy := [],
    offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.
-/
#guard_msgs in
example (context : ExecutionContext) (same : context.connection.state.database.catalog = sessions.raw.catalog) :
    Holds.reached (sql r"SELECT count(*) FROM sessions") context := by
  sql_holds [same]

/--
error: sql_holds needs the catalog of the database
  context.connection.state.database
Give a hint db.HasCatalog schema or an equation of its catalog, with a schema that has no variable.
-/
#guard_msgs in
example (context : ExecutionContext) :
    Holds.reached (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions)") context := by
  sql_holds

/--
error: sql_holds proves the goal that sql_run leaves for a claim holds q or holdsSince start q. Use it after sql_run, on the goal of the claim.
-/
#guard_msgs in
example (claim : Prop) (proof : claim) : claim := by
  sql_holds

end AssertionExamples
