import SqliteVerifier.ContractProofs
import Belay.Sqlite.Model.ModelLaws

set_option doc.verso true

/-! Application interpretations use structural model facts and retain flexible
logical contracts. They name tables; the catalog gives each name's position. -/

open Belay.Sqlite.Model

namespace SqliteVerifier

/-- Ordered physical rowids and optional projected cells. Use
{lean}`([] : LogicalRows)` for no rows; a missing cell differs from observed NULL. -/
abbrev LogicalRows := List (Int × List (Option Value))

/-- The catalog position of the table with the name, compared after SQLite's
ASCII folding, or {lean}`(none : Option Nat)` when no table has it. -/
def tablePosition (catalog : Catalog) (name : Identifier) : Option Nat := (catalog.findTable name).map Prod.fst

/-- Project the requested fields of the stored table with the name, retaining row
order and rowids. A name without a table in the catalog, or an absent stored
table, yields {name}`Option.none`; a present empty table yields
{lean}`(some [] : Option LogicalRows)`, so lost tables cannot look empty. -/
def observeTable (catalog : Catalog) (name : Identifier) (fields : List Identifier) (database : Database) :
    Option LogicalRows := do
  let position ← tablePosition catalog name
  (database.table position).map (·.project fields)

/-- Build an {name}`Interpretation` whose invariant requires {name}`Conforms` and a
table stored at the catalog position of the name that satisfies {name}`Covers`
for all requested fields. Observation uses {name}`observeTable`. Use an empty
field list to observe rowids only; the caller proves the logical contract's
validity. -/
def projectedInterpretation (profile : Profile) (catalog : Catalog) (name : Identifier) (fields : List Identifier) :
    Interpretation LogicalRows where
  invariant database := Conforms profile catalog database ∧ ∃ position table,
    tablePosition catalog name = some position ∧ database.table position = some table ∧ Covers table fields
  observe := observeTable catalog name fields

/-- Give every failure position and reason an interpretation with false invariant and
absent observation. Use this for success-only proofs; the verification conditions still
require proving modeled failures unreachable. -/
def unreachableFailures : FailureRepresentation Logical where
  interpretation := fun _ _ => ⟨fun _ => False, fun _ => none⟩

/-- For every logical contract, profile, failure position and reason, the
corresponding {name}`unreachableFailures` representation is sound. Every database
obligation is vacuous because its invariant is false; this does not establish a
failure invariant. The proof eliminates that impossible assumption. -/
theorem unreachableFailures_sound (contract : LogicalContract Logical) (profile : Profile) (position reason) :
    SoundRepresentation contract profile ((unreachableFailures (Logical := Logical)).interpretation position reason) := by
  intro database impossible
  exact False.elim impossible

/-- For every contract, profile, catalog, name and field list, assume the projection
of every valid table covering those fields satisfies the contract's validity.
Then {name}`projectedInterpretation` is a {name}`SoundRepresentation`. An empty
field list still requires that validity premise for its rowid-only projections.
The proof extracts the stored valid table and applies the supplied premise. -/
theorem projectedInterpretation_sound (contract : LogicalContract LogicalRows) (profile : Profile)
    (catalog : Catalog) (name : Identifier) (fields : List Identifier)
    (valid : ∀ table, table.Valid → Covers table fields → contract.valid (table.project fields)) :
    SoundRepresentation contract profile (projectedInterpretation profile catalog name fields) := by
  intro database invariant
  obtain ⟨conforms, position, table, located, present, covered⟩ := invariant
  exact ⟨conforms.2, table.project fields, by simp [projectedInterpretation, observeTable, located, present],
    valid table ((conforms.2.2.2 position).2 table present) covered⟩

end SqliteVerifier
