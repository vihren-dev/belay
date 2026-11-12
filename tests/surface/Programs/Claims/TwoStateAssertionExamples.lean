import Belay

set_option doc.verso true

/-! Fixtures of {lit}`tests/surface_assertion_examples_test.py` for the two-state assertions (ADR 0017, S6). A
query that names the schema {lit}`before` reads the initial database that the assertion is given, and every other
source reads the database that the context sees. The kernel checks that the default and the real-context
observations differ on a clock, that the assertion follows the reached database and not the start for a plain
source, that a query with no {lit}`before` source ignores the start, and that the fresh-run notation is the
primitive claim. -/
set_option maxRecDepth 4096

namespace AssertionExamples
open Belay.Sqlite Belay.Sqlite.Model Std.Do

/-- The start: two rows with an explicit rowid column. -/
def startRows : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- A complete environment with a distinct timestamp for each statement index. -/
def stamped : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    counters := Counters.newConnection }

/-- The fresh context of the start. -/
def entry : ExecutionContext := ExecutionContext.initial startRows stamped

/-- The context after a delete of the first row. -/
def afterRemoval : ExecutionContext :=
  entry.finish ((send (sql r"DELETE FROM t WHERE id = 1")).runFrom stamped.clock 0 entry.connection)

/-- The context after an insert of a third row. -/
def afterAddition : ExecutionContext :=
  entry.finish ((send (sql r"INSERT INTO t VALUES (3, 3)")).runFrom stamped.clock 0 entry.connection)

/-- The source {lit}`before.t` reads the start: the deleted row is there, and a plain source does not see it. -/
theorem before_reads_the_start :
    Holds.reachedSince (sql r"SELECT 1 FROM before.t WHERE id = 1") startRows afterRemoval ∧
      ¬ Holds.reached (sql r"SELECT 1 FROM t WHERE id = 1") afterRemoval := by decide +kernel

/-- A plain source reads the reached database: the added row is visible, and {lit}`before.t` lacks it. -/
theorem plain_source_reads_the_reached_database :
    Holds.reachedSince (sql r"SELECT 1 FROM t WHERE id = 3") startRows afterAddition ∧
      ¬ Holds.reachedSince (sql r"SELECT 1 FROM before.t WHERE id = 3") startRows afterAddition := by
  decide +kernel

/-- The initial database is an argument, not the reached one: with a different start the same context gives
a different answer for a {lit}`before` source. -/
theorem the_start_is_the_argument :
    ¬ Holds.reachedSince (sql r"SELECT 1 FROM before.t WHERE id = 1") (db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER)")
        afterRemoval := by decide +kernel

/-- Every row of the start survives an insert, and a delete loses one: the comparison of the start with the
reached database through the compound {lit}`EXCEPT`. -/
theorem except_compares_with_the_start :
    Holds.reachedSince (sql r"SELECT 1 WHERE NOT EXISTS (SELECT id, x FROM before.t EXCEPT SELECT id, x FROM t)")
        startRows afterAddition ∧
      ¬ Holds.reachedSince (sql r"SELECT 1 WHERE NOT EXISTS (SELECT id, x FROM before.t EXCEPT SELECT id, x FROM t)")
        startRows afterRemoval := by decide +kernel

/-- A clock read holds in the context that has a clock and not in the default observation, which has none,
also when the query reads the start. -/
theorem clock_disagrees_for_two_states :
    Holds.inContextSince (sql r"SELECT 1 FROM before.t WHERE CURRENT_TIMESTAMP IS NOT NULL") startRows entry ∧
      ¬ Holds.reachedSince (sql r"SELECT 1 FROM before.t WHERE CURRENT_TIMESTAMP IS NOT NULL") startRows entry := by
  decide +kernel

/-- A query with no {lit}`before` source ignores the start: the one-state assertion and the two-state assertions
with two different starts agree. -/
theorem a_plain_query_ignores_the_start :
    (Holds.reachedSince (sql r"SELECT 1 FROM t WHERE id = 3") startRows afterAddition ↔
      Holds.reached (sql r"SELECT 1 FROM t WHERE id = 3") afterAddition) ∧
    (Holds.reachedSince (sql r"SELECT 1 FROM t WHERE id = 3") (db! r"CREATE TABLE u(a)") afterAddition ↔
      Holds.reached (sql r"SELECT 1 FROM t WHERE id = 3") afterAddition) := by decide +kernel

/-- The assertion terms are the assertions on the context: {lit}`holdsSince` is the default one. -/
theorem terms_are_the_assertions :
    ((holdsSince startRows (sql r"SELECT 1 FROM before.t WHERE id = 1")) afterRemoval).down ↔
      Holds.reachedSince (sql r"SELECT 1 FROM before.t WHERE id = 1") startRows afterRemoval := Iff.rfl

/-- The fresh-run notation with the start is the primitive claim. -/
theorem notation_is_the_primitive_claim :
    ((send (sql r"DELETE FROM t WHERE id = 1")) ensuresFrom start =>
      ifOk (holdsSince start (sql r"SELECT 1 FROM before.t WHERE id = 1"))) =
    FreshEnsuresFrom (Runnable.toSql (send (sql r"DELETE FROM t WHERE id = 1"))) (fun _ => True)
      (fun start => ifOk (holdsSince start (sql r"SELECT 1 FROM before.t WHERE id = 1"))) := rfl

/-- The guard of the notation is the one-state {name}`Holds` of its query on the start. -/
theorem guarded_notation_is_the_primitive_claim :
    ((send (sql r"DELETE FROM t WHERE id = 1")) ensuresFrom start =>
      ifOk (holdsSince start (sql r"SELECT 1 FROM before.t WHERE id = 1")) where sql r"SELECT 1 FROM t") =
    FreshEnsuresFrom (Runnable.toSql (send (sql r"DELETE FROM t WHERE id = 1")))
      (fun db => Holds (sql r"SELECT 1 FROM t") db)
      (fun start => ifOk (holdsSince start (sql r"SELECT 1 FROM before.t WHERE id = 1"))) := rfl

/-- A claim that ignores the start is the claim of {lit}`ensures`. -/
theorem a_claim_without_the_start_is_ensures :
    ((send (sql r"DELETE FROM t WHERE id = 1")) ensuresFrom _start => andOk ⌜True⌝) =
    ((send (sql r"DELETE FROM t WHERE id = 1")) ensures andOk ⌜True⌝) := rfl

#print axioms before_reads_the_start
#print axioms plain_source_reads_the_reached_database
#print axioms the_start_is_the_argument
#print axioms except_compares_with_the_start
#print axioms clock_disagrees_for_two_states
#print axioms a_plain_query_ignores_the_start
#print axioms terms_are_the_assertions
#print axioms notation_is_the_primitive_claim
#print axioms guarded_notation_is_the_primitive_claim
#print axioms a_claim_without_the_start_is_ensures

end AssertionExamples
