import S6RulesEffects
import S6RulesQueryPattern
import S6CheckLabels

/-! A fixture module of `tests/surface_s6_check_programs_test.py`: the SQL checker on claims about programs
(ADR 0017, S6). The claims are triples with the fresh-run assertion, the equivalence of two programs, and the
migration query pattern. Each block between the markers {lit}`SQL-COMMAND-BEGIN` and {lit}`SQL-COMMAND-END` is the
output of one {lit}`#sql_check`. The test reads the blocks and replays the false ones in native SQLite. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option sql.check false

namespace S6RulesEffects
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The update that adds 2, so it differs from {name}`bump` on every database with the item row. -/
def bumpTwice : Script := sql r"UPDATE items SET qty = qty + 2 WHERE id = ?1" (Value.integer 1)

/-- The claim that the update of {name}`bump` leaves the given rows in the items table of {name}`sample`. -/
def leavesRows (rows : List (List Value)) : Prop :=
  FreshEnsures (send bump) (fun db => db = sample)
    (ifOk (fun final => ⌜tableValues 0 final.connection = rows⌝ : ContextAssertion))

labelled_sql "triple-proved" in
#sql_check leavesRows [[.integer 1, .integer 6]]

labelled_sql "triple-false" in
#sql_check leavesRows [[.integer 1, .integer 7]]

labelled_sql "lean-continuation-false" in
#sql_check ∀ n : Value, FreshEnsures (send bump >>= fun _ => pure n) (fun db => db = sample)
    (ifOk (fun final => ⌜tableValues 0 final.connection = [[.integer 1, .integer 7]]⌝ : ContextAssertion))

labelled_sql "equiv-proved" in
#sql_check Sql.Equiv (send bump) (send bump)

set_option sql.checkBudget 400000 in
labelled_sql "equiv-false" in
#sql_check Sql.Equiv (send bump) (send bumpTwice) with (db := sample)

set_option sql.checkBudget 400000 in
labelled_sql "equiv-at-false" in
#sql_check ∀ db : Database, db = sample → ∀ env : Env, env.Complete →
  Sql.EquivAt (send bump) (send bumpTwice) (ExecutionContext.initial db env)

-- Shrinking needs about 280000 units and gets half of what is left, so it runs out. The refutation that was
-- certified and explained before the shrinking stays as the result.
set_option sql.checkBudget 200000 in
labelled_sql "equiv-shrink-exhausted" in
#sql_check Sql.Equiv (send bump) (send bumpTwice) with (db := sample)

set_option sql.checkBudget 1000 in
labelled_sql "budget-unknown" in
#sql_check leavesRows [[.integer 1, .integer 7]]

labelled_sql "undecidable-unknown" in
#sql_check ∀ db : Database, db = sample → ∀ env : Env, env.Complete →
  (send bump).check (fun _ _ => ∀ k : Nat, k + 1 = 0) (ExecutionContext.initial db env)

end S6RulesEffects

namespace S6RulesQueryPattern
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A read of all columns, which sees the column that the migration adds. -/
def starRead : Script := sql r"SELECT * FROM items"

set_option sql.checkBudget 400000 in
labelled_sql "migration-star-false" in
#sql_check Migration.PreservesAt (send expansion) (fun _ => True) (send starRead) initial

set_option sql.checkBudget 400000 in
labelled_sql "migration-lookup-unknown" in
#sql_check ∀ name : Value, Migration.PreservesAt (send expansion) (fun _ => True) (send (lookup name)) initial

end S6RulesQueryPattern
