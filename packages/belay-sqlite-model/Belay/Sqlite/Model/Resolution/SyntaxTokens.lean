import Belay.Sqlite.Model.Declarations

set_option doc.verso true

/-! The places of the name tokens in the source text of a result column. SQLite keeps the text
of an unaliased expression as the name of a view column, and a rename of a table or column
rewrites the name tokens of that text. The frontend therefore records, for each name token of the
text, where it stands in the text, how it was quoted, and the node paths of the name in the
statement, among which is the path that the name trace reports for the same name. The frontend
records them in the body of a stored view, whose column names are such texts; the text of a result
column elsewhere has no tokens. The trace and the resolved forms do not read the tokens. -/

namespace Belay.Sqlite.Model.Syntax

/-- How an identifier was written: unquoted, or in double quotes, brackets or backticks.
SQLite reads an unquoted {lit}`TRUE` or {lit}`FALSE` as a keyword, and a double-quoted
name as a string when no column has it; brackets and backticks only quote. -/
inductive QuoteKind where
  /-- An unquoted identifier, such as {lit}`a`. -/
  | none
  /-- An identifier in double quotes, such as {lit}`"a"`. -/
  | double
  /-- An identifier in brackets, such as {lit}`[a]`. -/
  | bracket
  /-- An identifier in backticks, such as {lit}`` `a` ``. -/
  | backtick
  /-- A string in single quotes where the grammar expects a name, such as {lit}`t.'a'`. An
  expression never holds an identifier of this kind: a string there is a literal. -/
  | single
  deriving Repr, DecidableEq

/-- One name token of a source text. Its {lit}`start` and {lit}`stop` are byte offsets in the
text, so the text between them is the name as written, with its quotes. Its {lit}`paths` are the
node paths of the name in the expression of the result column ({lit}`NameOccurrence.path` of the
name trace, without the steps up to the expression), or, when {lit}`subquery` is the index of an
indexed subquery inside the text, in that subquery. The frontend records every token that is a
single name, including the names that are no column or table, such as aliases; a client
chooses the token that has the path of an occurrence. -/
structure NameToken where
  /-- The index of the indexed subquery that holds the name, or none for a name of the expression
  itself. -/
  subquery : Option Nat := none
  /-- The node paths of the name, from the expression or from the subquery. The range of a
  token can be the range of several nodes, such as an identifier and its name part, and the name
  trace uses the path of the node that it visits, so a token lists the path of every node with
  its range. -/
  paths : List (List Nat)
  /-- The first byte of the token in the text. -/
  start : Nat
  /-- The byte after the token in the text. -/
  stop : Nat
  /-- How the token was quoted. -/
  quote : QuoteKind
  deriving Repr, DecidableEq

/-- A source text as written, with the places of its name tokens. A text without recorded tokens
is a plain string, which the coercion from {name}`String` turns into a text without tokens. -/
structure SourceText where
  /-- The text, as it is the name of a view column. It is empty for a CHECK constraint whose label is the name of
  the constraint. -/
  text : String := ""
  /-- The name tokens of the text, in text order. -/
  tokens : List NameToken := []
  deriving Repr, DecidableEq

/-- A plain string is a text without recorded tokens. -/
instance : Coe String SourceText := ⟨fun text => { text }⟩

end Belay.Sqlite.Model.Syntax
