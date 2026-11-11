import Belay.Sqlite.Model.Queries.Evaluation.PragmaSource
import Belay.Sqlite.Model.Shared.Resolved.QueryForm

set_option doc.verso true

/-! The resolved form of a single-table query of ADR 0012, slice 1: what
{lit}`resolve` gives for a {lit}`SELECT` and what the Queries level evaluates: its
sources with their joins, and its parts over the values of {lit}`ResolvedExprForm.lean`.
Names are already table positions, and the affinity rules of a comparison are
already applied to its literal operands, so evaluation needs no catalog. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether the source is {lit}`json_each`. -/
def Source.isEach : Source → Bool
  | .each .. => true
  | .table _ | .initialTable _ | .subquery .. | .pragma _ => false

/-- Whether the source reads the fixed initial database of a two-state query
({name}`Source.initialTable`). -/
def Source.isInitial : Source → Bool
  | .initialTable _ => true
  | .table _ | .each .. | .subquery .. | .pragma _ => false

/-- Whether the source reads the rows of the current database: a table, or the rows of a table-valued
pragma over it. The sources {lit}`json_each` and a derived table read only the rows so far and the
subqueries, and a table of the initial database never reads the current database. -/
def Source.readsCurrent : Source → Bool
  | .table _ | .pragma _ => true
  | .initialTable _ | .each .. | .subquery .. => false

/-- The first source of a {lit}`FROM`: the table at the catalog position, as an inner join
without a condition. -/
def QuerySource.first (position : Nat) : QuerySource := { kind := .inner, source := .table position, condition := none }

/-- The indexes of the terms of a compound, from left to right. -/
def Compound.terms (compound : Compound) : List Nat :=
  compound.first :: compound.rest.map (·.2)

/-- Whether a query reads the table at the catalog position directly, as one of its sources. -/
def Query.readsTable (position : Nat) (query : Query) : Bool :=
  query.sources.any (·.source == .table position)

/-- Whether a query has a source in the initial database ({name}`Source.isInitial`). The
subqueries of a statement are separate queries; {lit}`Statement.readsInitial` collects them. -/
def Query.readsInitial (query : Query) : Bool :=
  query.sources.any (·.source.isInitial)

/-- Whether a query has a source in the current database ({name}`Source.readsCurrent`). -/
def Query.readsCurrent (query : Query) : Bool :=
  query.sources.any (·.source.readsCurrent)

end Belay.Sqlite.Model.Resolved
