import RebuildKeeps
import RebuildSucceedsFinish

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! Claim 2 of the guide's table rebuild (ADR 0017, S6, part 3): the rebuild {lit}`makeStrict` succeeds on every
database of the guide's schema whose customers fit the STRICT types of the new table. The success covers the actual
run and every branch
of the INSERT from a query. The steps of the rebuild keep the facts of {lit}`RebuildKeepsInvariant` and the facts about
the customers of {lit}`RebuildSucceedsCopy`, and each step continues without an error
({lit}`RebuildSucceedsSteps`, {lit}`RebuildSucceedsFinish`); {lit}`sendStatements_succeedsFrom` turns this into success
of the script. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For a database: every row of the customers fits the STRICT types of the new customers
({name}`LiteralData.typesFit` on {name}`strictShape`): an integer id, a name that is text or NULL, and an email
that is text or NULL. The rows are those of the table that the name {lit}`customers` finds, wherever it is. A
database without such a table satisfies it. -/
def StrictRows (db : Database) : Prop :=
  ∀ (position : Nat) (customers : Table), db.raw.tableNamed customersName = some (position, customers) →
    ∀ row ∈ customers.rows, LiteralData.typesFit strictShape row = true

/-- The rebuild succeeds on every database whose catalog is the guide's schema and whose customers all fit the STRICT
types of the new table, in every complete environment, on the actual run and on every branch. The rows are otherwise
unrestricted. Where the database has a customer with a cell that does not fit the STRICT type of its column, for
example a blob email, the claim requires nothing; there the INSERT from a query fails. NULL fits every type, so a
customer without a name is within the premise. Proof sketch: {name}`sendStatements_succeedsFrom` with the facts {name}`Good`; the facts
hold at the start, and {name}`good_advance` shows that each step continues without an error and keeps them. -/
theorem makeStrict_succeeds :
    Succeeds makeStrict (fun db => db.raw.catalog = sample.raw.catalog ∧ StrictRows db) := by
  intro db ⟨pre, fits⟩ env complete
  obtain ⟨sessions, namedSessions, _⟩ := Database.tableNamed_of_hasCatalog (schema := sample) pre
    (name := sessionsName) (position := 1) (by with_unfolding_all exact rfl)
  obtain ⟨customers, namedCustomers, _⟩ := Database.tableNamed_of_hasCatalog (schema := sample) pre
    (name := customersName) (position := 0) (by with_unfolding_all exact rfl)
  have start : Good sessions customers 0 (db.raw.connection env.counters) :=
    ⟨kept_start pre namedSessions, ResolveState.tableAtPrefix_zero (Database.tableNamed_some namedCustomers).2, fun h => by omega⟩
  exact sendStatements_succeedsFrom makeStrict.statements (Good sessions customers) env.clock 0
    (db.raw.connection env.counters) ⟨db.valid, fun _ shown => by simp [Database.Raw.connection] at shown⟩ start
    (good_advance env.clock sessions customers (fits 0 customers namedCustomers))

#print axioms makeStrict_succeeds

end RebuildGuide
