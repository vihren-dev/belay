import Belay.Sqlite.Declarations
import Belay.Sqlite.ClockText

set_option doc.verso true

/-! The DEFAULT of a catalog column after resolution (ADR 0013, decision D3). Resolution of
CREATE TABLE and ADD COLUMN evaluates a written default once and stores the values that
INSERT and ADD COLUMN use, with the default's source text, so the catalog does not hold
the pre-resolution syntax and execution does not evaluate it again. -/

namespace Belay.Sqlite

/-- The value that an INSERT gives a column whose value it omits, before the column's
affinity applies: a value, or SQLite's {lit}`hex literal too big: %s` preparation error,
which SQLite reports when it prepares the INSERT, not when it creates the table. -/
inductive DefaultInsert where
  /-- The default's value before affinity, for example {lean}`DefaultInsert.value (.integer 7)`. -/
  | value (value : Value)
  /-- An oversized hexadecimal literal, with its text as written. -/
  | hexLiteralTooBig (text : String)
  deriving Repr, DecidableEq

/-- What a default is: a literal with the value that INSERT uses and the value that old
rows read after ADD COLUMN, which SQLite computes by different paths (for example
{lit}`TEXT DEFAULT 1.50` inserts {lit}`1.5` and reads back {lit}`1.50`); or a time
keyword such as {lit}`CURRENT_TIMESTAMP`, whose value is the statement's clock. -/
inductive DefaultForm where
  /-- A literal default: its INSERT value, and its read-back value for old rows, already
  stored with the column's affinity. -/
  | literal (insert : DefaultInsert) (readBack : Value)
  /-- A time keyword default. -/
  | clock (keyword : TimeKeyword)
  deriving Repr, DecidableEq

/-- A resolved column default with the source text that {lit}`sqlite_schema` shows, the
text after {lit}`DEFAULT` without the parentheses of the DEFAULT production. For example,
{lean}`({ form := .literal (.value (.integer 7)) (.integer 7), sourceText := "7" } : ColumnDefault)`
is {lit}`DEFAULT 7` of an INTEGER column. -/
structure ColumnDefault where
  /-- The resolved values of the default. -/
  form : DefaultForm
  /-- The default's spelling as written. -/
  sourceText : String
  deriving DecidableEq

/-- Print a default as a constructor application, so that generated nested catalog terms
keep valid Lean indentation when the form spans several lines. -/
instance : Repr ColumnDefault where
  reprPrec value prec := Repr.addAppParen
    ("Belay.Sqlite.ColumnDefault.mk " ++ reprArg value.form ++ " " ++ reprArg value.sourceText) prec

end Belay.Sqlite
