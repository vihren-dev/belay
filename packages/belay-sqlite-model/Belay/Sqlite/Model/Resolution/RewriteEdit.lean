import Belay.Sqlite.Model.Resolution.SyntaxReindex

set_option doc.verso true

/-! The edit of a rename on syntax (ADR 0019, D4): the place of one name in an object as written,
the name that SQLite finds there, and the name that replaces it. A rename decides its edits from the
name trace of the object ({lit}`NameOccurrence.path`), so an edit finds its name by the path of the
occurrence and never by its spelling. The spelling of the old name only guards the edit: a path that
leads to another name, or to no name, is a failure of the rewrite, which a rename reports as a
restriction of the model and not as a wrong rewrite. -/

namespace Belay.Sqlite.Model.Syntax

/-- How SQLite writes the new name into the text of an object. {lit}`RENAME TO` writes the new name
of a table in double quotes. {lit}`RENAME COLUMN` writes the new name as it was written in the
statement when the name it replaces is an unquoted identifier, and in double quotes otherwise. -/
inductive RenameStyle where
  /-- A table: always in double quotes. -/
  | table
  /-- A column; {lit}`newQuoted` tells whether the new name was written with a quote. -/
  | column (newQuoted : Bool)
  deriving Repr, DecidableEq

/-- The quote of a name that replaces a name written with the quote {lit}`old`. -/
def RenameStyle.quote : RenameStyle → QuoteKind → QuoteKind
  | .table, _ => .double
  | .column newQuoted, old => if !newQuoted && old == .none then .none else .double

/-- The name as it stands in a text with the quote: the quote characters around it, and a quote
character in the name doubled. For example, {lean}`Identifier.ofString "a\"b"` in double quotes is
{lit}`"a""b"`. -/
def QuoteKind.render (quote : QuoteKind) (name : String) : String :=
  match quote with
  | .none => name
  | .double => "\"" ++ name.replace "\"" "\"\"" ++ "\""
  | .bracket => "[" ++ name ++ "]"
  | .backtick => "`" ++ name.replace "`" "``" ++ "`"
  | .single => "'" ++ name.replace "'" "''" ++ "'"

/-- One name to replace: where it stands, the name that it has, the name that replaces it and the
way SQLite writes the new name. -/
structure NameEdit where
  /-- The node path of the name in the object, as {lit}`NameOccurrence.path` has it. -/
  path : List Nat
  /-- The name now. -/
  old : Identifier
  /-- The new name. -/
  new : Identifier
  /-- How the new name is written. -/
  style : RenameStyle
  /-- Whether the edit writes the name as a single-quoted string literal instead of renaming it. SQLite does
  this in every view and trigger at every column rename ({lit}`renameQuotefix`): a double-quoted name that no column
  has is a string literal, and it must stay one when a rename gives a column that name. Then {lit}`old` is
  the name and {lit}`new` and {lit}`style` have no effect. -/
  fixQuote : Bool := false
  deriving Repr, DecidableEq

/-- The edit with its path moved below the node at the prefix. -/
def NameEdit.below (edit : NameEdit) (prefix_ : List Nat) : NameEdit := { edit with path := prefix_ ++ edit.path }

/-- The name of the edit if the name at hand is the name it replaces; none for another name. -/
def NameEdit.replace? (edit : NameEdit) (name : Identifier) : Option Identifier :=
  if name == edit.old then some edit.new else none

/-- Replace the element at the index of a list with the result of the change; none when the list
is shorter or the change fails. -/
def replaceNth? (change : α → Option α) : Nat → List α → Option (List α)
  | _, [] => none
  | 0, item :: rest => (change item).map (· :: rest)
  | index + 1, item :: rest => (replaceNth? change index rest).map (item :: ·)

end Belay.Sqlite.Model.Syntax
