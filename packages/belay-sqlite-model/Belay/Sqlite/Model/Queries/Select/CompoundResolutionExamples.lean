import Belay.Sqlite.Model.Queries.Evaluation.CollationExamples
import Belay.Sqlite.Model.Queries.Select.CollationExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CompoundResolutionExamples

open Belay.Sqlite.Model Syntax Resolution.CollationExamples

/-- The rows {lit}`('1', 'a')` into {lit}`t`, {lit}`(1, 'A')` into {lit}`u`, and {lit}`'C'` and
{lit}`'a'` into {lit}`w`. -/
def filled : List Syntax.Statement :=
  [insertText (name! "t") [[49], [97]], insertText (name! "u") [[49], [65]], insertText (name! "w") [[67]],
   insertText (name! "w") [[97]]]

/-- A term {lit}`SELECT columns [FROM table] [WHERE filter]` inside the query {lit}`parent`. -/
def term (columns : List ResultColumn) (table : Option String := none) (parent : Option Nat := none)
    (filter : Option Expr := none) : Subquery :=
  { columns, source := table.map fun text => { table := Identifier.ofString text, alias := none }, joins := [], filter,
    groupBy := [], orderBy := [], limit := none, offset := none, parent }

/-- The compound of the terms at the indexes {lit}`first` to {lit}`first + n`, with the
operators between them. -/
def chain (first : Nat) (operators : List CompoundOperator) : Compound :=
  { first, rest := operators.zipIdx.map fun (operator, index) => (operator, first + index + 1) }

/-- A compound statement over its terms, which are the first subqueries, then the other
subqueries. -/
def compound (operators : List CompoundOperator) (terms : List Subquery) (orderBy : List OrderTerm := [])
    (others : List Subquery := []) : Syntax.Statement :=
  .select [] none [] none [] orderBy none none (terms ++ others) none false (some (chain 0 operators))

/-- A compound subquery of the statement's query, at index 0, over the terms after it. -/
def compoundSubquery (operators : List CompoundOperator) (orderBy : List OrderTerm := []) : Subquery :=
  { term [] with orderBy, compound := some (chain 1 operators) }

/-- A result column with an alias. -/
def named (value : Expr) (alias : String) : ResultColumn := .expression value (some (Identifier.ofString alias)) alias

/-- An ascending {lit}`ORDER BY` term. -/
def ascending (value : Expr) : OrderTerm := { expression := value, descending := false }

/-- The integer literal of a text. -/
def num (text : String) : Expr := .numeric text

-- The COLLATE exception, over w with 'C' and 'a': SELECT 'b' AS x, 1 AS y UNION SELECT n, 1 FROM w
-- ORDER BY y COLLATE BINARY, x sorts x under BINARY, the collation of the left-most term.
/-- The compound of outcome 7's exception with an operator and an {lit}`ORDER BY`. -/
def exception (operator : CompoundOperator) (orderBy : List OrderTerm) : Syntax.Statement :=
  compound [operator] [term [named (.string [98]) "x", named (num "1") "y"],
    term [shown (ref (name! "n")), shown (num "1")] "w"] orderBy

/-- {lit}`SELECT a COLLATE NOCASE ..., then the columns, FROM t EXCEPT SELECT a ... FROM t`
with the {lit}`ORDER BY`; the first column has its text as written. -/
def renamed (columns : List ResultColumn) (orderBy : List OrderTerm) : Syntax.Statement :=
  compound [.except] [term (.expression (.collate (ref (name! "a")) (name! "NOCASE")) none "a COLLATE NOCASE" :: columns) "t",
    term (shown (ref (name! "a")) :: columns.map fun _ => shown (num "1")) "t"] orderBy

/-- {lit}`SELECT value IN (compound)` over the terms. -/
def inCompound (value : Expr) (operators : List CompoundOperator) (terms : List Subquery)
    (orderBy : List OrderTerm := []) : Syntax.Statement :=
  .select [shown (.inQuery value 0 false)] none [] none [] [] none none (compoundSubquery operators orderBy :: terms)

end Belay.Sqlite.Model.Resolution.CompoundResolutionExamples
