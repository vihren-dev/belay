import Belay.Sqlite.Model.Resolution.SyntaxReindex
import Belay.Sqlite.Model.Resolution.CommonTableErrors

set_option doc.verso true

/-! Lexical WITH names over the existing indexed query list. Lookup includes forward
definitions in the same clause. Column bindings remain a separate, per-use query scope. -/

namespace Belay.Sqlite.Model

/-- The query indexes that declare a WITH name in {lit}`owner`'s scope, in written order.
Use {lean}`(none : Option Nat)` for definitions attached to the statement itself. -/
def commonTablesIn (queries : List Syntax.Subquery) (owner : Option Nat) : List Nat :=
  (List.range queries.length).filter fun index =>
    (queries[index]?).any fun query => query.parent == owner && query.commonTable.isSome

/-- Find a CTE by its case-insensitive name, starting at the query's own WITH clause
and then walking its written parents. The bound is the number of syntax queries plus one;
it prevents a malformed parent cycle from making lookup diverge. -/
def findCommonTable (queries : List Syntax.Subquery) (name : Identifier) :
    Nat → Option Nat → Option Nat
  | 0, _ => none
  | fuel + 1, owner =>
    match (commonTablesIn queries owner).find? fun index =>
        ((queries[index]?).bind (·.commonTable)).any (·.name.folded == name.folded) with
    | some index => some index
    | none => match owner with
      | none => none
      | some index => match queries[index]? with
        | none => none
        | some query => findCommonTable queries name fuel query.parent

/-- The first repeated CTE name in one WITH clause, including unused definitions.
Names in nested clauses can shadow outer names and do not conflict with them. -/
def duplicateCommonTable (queries : List Syntax.Subquery) : Option CommonTableError :=
  (List.range queries.length).findSome? fun index => do
    let query ← queries[index]?
    let definition ← query.commonTable
    if (queries.take index).any fun earlier => earlier.parent == query.parent &&
        earlier.commonTable.any (·.name.folded == definition.name.folded) then
      some (.duplicate definition.name)
    else none

end Belay.Sqlite.Model
