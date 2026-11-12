import Belay.Sqlite.Model.Queries.Select.CompoundResolutionExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.DerivedResolutionExamples

open Syntax

/-- A derived source whose SELECT is in the statement's indexed query list. -/
def derived (index : Nat) (alias : Option String := none) : TableReference :=
  { table := name! "", alias := alias.map Identifier.ofString, query := some index }

/-- A statement that reads one derived source, with arbitrary output expressions. -/
def fromDerived (columns : List ResultColumn) (subqueries : List Subquery) : Syntax.Statement :=
  .select columns (some (derived 0 (some "d"))) [] none [] [] none none subqueries

end Belay.Sqlite.Model.Resolution.DerivedResolutionExamples
