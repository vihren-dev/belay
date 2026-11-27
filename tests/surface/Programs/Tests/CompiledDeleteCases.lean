import Belay

set_option sql.check false

set_option doc.verso true

namespace CompiledDeleteCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open scoped Belay.Sqlite.LastOutput

/-- Two duplicates, a NULL and an independent table distinguish the effects of successive writes. -/
private def sample : Database := db! r"
  CREATE TABLE items (x INTEGER);
  INSERT INTO items VALUES (1), (1), (NULL), (2);
  CREATE TABLE other (x INTEGER);
  INSERT INTO other VALUES (9);"

/-- Inspect the certified plan's actual output on the example database. -/
private def last? (script : Script) : Option Output := do
  let plan ← script.compileLastOutput? sample
  (plan.val sample Env.newConnection).1

/-- Terminal DELETE counts matches, including duplicates, and a second DELETE counts survivors.
Proof sketch: compute on the sample. A NULL comparison does not remove the NULL row. -/
theorem counts :
    let first := sql r"DELETE FROM items WHERE x = ?1" (Value.integer 1)
    last? first = some (.done 2) ∧
    last? (first ++ (sql r"DELETE FROM items WHERE x = ?1" Value.null)) = some (.done 0) ∧
    last? (first ++ (sql r"DELETE FROM items")) = some (.done 2) := by decide +kernel

/-- The read after two bound deletes sees both effects and uses its own binding.
Proof sketch: compute the projected value for the one remaining NULL row. -/
theorem remaining :
    let first := sql r"DELETE FROM items WHERE x = ?1" (Value.integer 1)
    let second := sql r"DELETE FROM items WHERE x = ?1" (Value.integer 2)
    let read := sql r"SELECT ?1 FROM items WHERE x IS NULL" (Value.integer 7)
    last? (first ++ second ++ read) = some (.rows [[.integer 7]]) := by decide +kernel

/-- On every database with this catalog, deleting from items preserves the last output
of a scan of other. Proof sketch: compile both scripts and compare the unaffected scan. -/
theorem other_table :
    (sql r"DELETE FROM items"); (sql r"SELECT x FROM other") ~ (sql r"SELECT x FROM other") on sample := by
  sql_run

/-- Operand order, parentheses and the split between DELETE and SELECT yield one set of
sorted clauses. Proof sketch: compare the actual compiler outputs by reflexivity. -/
example :
    let del := sql r"DELETE FROM items WHERE x IS NULL"
    let read := sql r"SELECT x FROM items WHERE x > 0 AND x < 10"
    let reference := sql r"SELECT x FROM items WHERE (x < 10 AND x IS NOT NULL) AND (x > 0 AND x < 10)"
    (((del ++ read).compileScan? sample).get (by rfl)).val =
      ((reference.compileScan? sample).get (by rfl)).val := rfl

/-- SQL NOT of NULL still yields NULL. A DELETE keeps the NULL row when its comparison
is unknown. Proof sketch: inspect the outputs on the sample, which contains one NULL. -/
example :
    let deleted := (sql r"DELETE FROM items WHERE x = 1") ++ (sql r"SELECT x FROM items WHERE x IS NULL")
    let negated := sql r"SELECT x FROM items WHERE NOT (x = 1) AND x IS NULL"
    last? deleted = some (.rows [[.null]]) ∧ last? negated = some (.rows []) := by decide +kernel

/-- RETURNING, fallible expressions, subqueries and trigger writes require different
certificates. Proof sketch: compute the four compiler decisions. -/
theorem declined :
    let triggered := db! r"CREATE TABLE items (x);
      CREATE TABLE log (x); CREATE TRIGGER audit AFTER DELETE ON items BEGIN INSERT INTO log VALUES (old.x); END;"
    ((sql r"DELETE FROM items RETURNING x").compileLastOutput? sample).isNone ∧
    ((sql r"DELETE FROM items WHERE abs(x)").compileLastOutput? sample).isNone ∧
    ((sql r"DELETE FROM items WHERE x IN (SELECT x FROM other)").compileLastOutput? sample).isNone ∧
    ((sql r"DELETE FROM items").compileLastOutput? triggered).isNone := by decide +kernel

#print axioms counts
#print axioms remaining
#print axioms other_table
#print axioms declined
end CompiledDeleteCases
