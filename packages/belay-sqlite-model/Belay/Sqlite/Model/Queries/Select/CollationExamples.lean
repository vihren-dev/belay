import Belay.Sqlite.Model.Queries.Preparation.CollationExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CollationExamples

open Belay.Sqlite.Model Syntax

-- Names ignore ASCII case, and each name reads back.
#guard [name! "NoCase", name! "rtrim", name! "BINARY", name! "nocase2"].map Collation.named? ==
  [some .nocase, some .rtrim, some .binary, none]
#guard [Collation.binary, .nocase, .rtrim].all fun collation =>
  Collation.named? (Identifier.ofString collation.sqlName) == some collation

/-- An INSERT of one row of text cells into a table. -/
def insertText (table : Identifier) (cells : List (List UInt8)) : Syntax.Statement :=
  .insert table none [cells.map .string] [] none []

/-- The rows {lit}`('a', 'a ', 'a')`, {lit}`('B', 'b', 'B')` and {lit}`('A', 'a', 'a')` into
{name}`tableC`, in this order, and {lit}`('a', 'b')` into {name}`tableW`. -/
def filledC : List Syntax.Statement :=
  [insertText (name! "c") [[97], [97, 32], [97]], insertText (name! "c") [[66], [98], [66]],
   insertText (name! "c") [[65], [97], [97]], insertText (name! "w") [[97], [98]]]

/-- An unqualified column. -/
def ref (name : Identifier) : Expr := .identifier name .none

/-- A result column of an expression. -/
def shown (value : Expr) : ResultColumn := .expression value none "e"

/-- A {lit}`SELECT` from one table. -/
def selectFrom (table : Identifier) (columns : List ResultColumn) (filter : Option Expr := none)
    (groupBy : List Expr := []) (orderBy : List OrderTerm := []) (joins : List Join := []) : Syntax.Statement :=
  .select columns (some { table, alias := none }) joins filter groupBy orderBy none none

end Belay.Sqlite.Model.Resolution.CollationExamples
