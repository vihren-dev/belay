import RebuildKeeps
import RebuildSucceedsFinish

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! Claim 2 of the guide's table rebuild (ADR 0017, S6, part 3): the rebuild {lit}`requireName` succeeds on every
database of the guide's schema in which no customer lacks a name. The success covers the actual run and every branch
of the INSERT from a query. The steps of the rebuild keep the facts of {lit}`RebuildKeepsInvariant` and the facts about
the customers of {lit}`RebuildSucceedsCopy`, and each step continues without an error
({lit}`RebuildSucceedsSteps`, {lit}`RebuildSucceedsFinish`); {lit}`sendStatements_succeedsFrom` turns this into success
of the script. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For a database: every customer in it has a name that is not NULL. The name is the cell at position 1 of the row, in
the table that the name {lit}`customers` finds, wherever it is. A database without such a table satisfies it. -/
def NoNullName (db : Database) : Prop :=
  ∀ (position : Nat) (customers : Table), db.raw.tableNamed customersName = some (position, customers) →
    ∀ row ∈ customers.rows, row.values[1]? ≠ some .null

/-- For every database of the guide's schema: the name of the customers finds a table at position 0. Proof sketch: the
sample finds the name at position 0, and the lookup depends on the catalog only. -/
theorem customers_found {db : Database} (pre : db.raw.catalog = sample.raw.catalog) :
    ∃ customers, db.raw.tableNamed customersName = some (0, customers) := by
  have atZero : (sample.raw.catalog.findTable customersName).map (·.1) = some 0 := by decide +kernel
  cases lookup : db.raw.catalog.findTable customersName with
  | none => rw [← pre, lookup] at atZero; simp at atZero
  | some found =>
    obtain ⟨place, shape⟩ := found
    rw [← pre, lookup] at atZero
    simp only [Option.map_some, Option.some.injEq] at atZero
    subst atZero
    exact ⟨_, by rw [Database.tableNamed_of_findTable lookup, Database.table_of_findTable _ _ _ _ lookup]; rfl⟩

/-- The rebuild succeeds on every database whose catalog is the guide's schema and in which no customer lacks a name,
in every complete environment, on the actual run and on every branch. The rows are otherwise unrestricted. Where the
database has a customer without a name, the claim requires nothing; there the INSERT from a query fails on the
NOT NULL of the new table. Proof sketch: {name}`sendStatements_succeedsFrom` with the facts {name}`Good`; the facts
hold at the start, and {name}`good_advance` shows that each step continues without an error and keeps them. -/
theorem requireName_succeeds :
    Succeeds requireName (fun db => db.raw.catalog = sample.raw.catalog ∧ NoNullName db) := by
  intro db ⟨pre, noNull⟩ env complete
  obtain ⟨sessions, namedSessions⟩ := sessions_found pre
  obtain ⟨customers, namedCustomers⟩ := customers_found pre
  have start : Good sessions customers 0 (db.raw.connection env.counters) :=
    ⟨kept_start pre namedSessions, fun _ => namedCustomers, fun h => by omega⟩
  exact sendStatements_succeedsFrom requireName.statements (Good sessions customers) env.clock 0
    (db.raw.connection env.counters) ⟨db.valid, fun _ shown => by simp [Database.Raw.connection] at shown⟩ start
    (good_advance env.clock sessions customers (noNull 0 customers namedCustomers))

#print axioms requireName_succeeds

end RebuildGuide
