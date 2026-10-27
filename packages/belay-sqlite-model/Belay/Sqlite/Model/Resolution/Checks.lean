import Belay.Sqlite.Model.Resolution.SyntaxTokens
import Belay.Sqlite.Model.Resolution.ResolvedExprForm

set_option doc.verso true

/-! The CHECK constraints and the generated columns of a table (ADR 0014, D2 and D5). A
CHECK is a condition over a row of its table, resolved once when the table is defined,
and the label that SQLite reports when the condition is false. Execution checks it on
every row that a write stores, after it computes the generated columns of the row. -/

namespace Belay.Sqlite.Model

/-- What a name token of the text of a CHECK constraint stands for. -/
inductive LabelTarget where
  /-- The table that holds the constraint, as the qualifier of a column. -/
  | table
  /-- The column at the position in the table. -/
  | column (position : Nat)
  deriving Repr, DecidableEq

/-- One name token of the text of a CHECK constraint that the resolver bound to the table or to a column
of it. The bytes {lit}`start` to {lit}`stop` of the text are the token as written, with its quotes. -/
structure LabelName where
  /-- The first byte of the token in the text. -/
  start : Nat
  /-- The byte after the token in the text. -/
  stop : Nat
  /-- How the token was quoted. -/
  quote : Syntax.QuoteKind
  /-- What the token stands for. -/
  target : LabelTarget
  deriving Repr, DecidableEq

/-- The source text of an unnamed CHECK constraint with the tokens that name the table or a column.
SQLite keeps the text, and a rename of the table or of a column rewrites these tokens in it; the label
that SQLite reports is the dequoted text ({lit}`CHECK constraint failed: label`). -/
structure CheckText where
  /-- The text between the parentheses, without outer white space. -/
  text : String
  /-- The name tokens of the text that name the table or a column, in text order. -/
  names : List LabelName
  deriving Repr, DecidableEq

/-- One CHECK constraint: its condition over a row of the table and the label of
{lit}`CHECK constraint failed: label`. For example, {lit}`CHECK (a > 0)` on the first
column has the condition {lean}`Resolved.Expr.compare .gt none (.column 0) (.literal (.integer 0))`
and the label {lit}`a > 0`. -/
structure CheckConstraint where
  /-- The condition over the row, resolved as a {lit}`WHERE` condition of the table. -/
  condition : Resolved.Expr
  /-- The label that SQLite reports when the condition is false. -/
  label : String
  /-- The source text of the constraint, or none when a {lit}`CONSTRAINT name` gives the label. -/
  source : Option CheckText := none
  deriving Repr, DecidableEq

/-- How a generated column is computed: its expression over a row of the table and whether
it is {lit}`STORED`. For example, {lit}`b AS (a * 2)` on a table {lit}`(a, b)` has the expression
{lean}`Resolved.Expr.arithmetic .multiply (.column 0) (.literal (.integer 2))` and is
{lit}`VIRTUAL`. The model stores the values of both kinds, as they read the same (ADR 0014,
D5). -/
structure GeneratedColumn where
  /-- The expression over a row of the table. -/
  expression : Resolved.Expr
  /-- Whether the column is {lit}`STORED`; false for {lit}`VIRTUAL`. -/
  stored : Bool
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
