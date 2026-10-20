import Belay.Sqlite.Declarations
import Belay.Sqlite.Operators

set_option doc.verso true

/-! Expressions and clauses as written, before name resolution; {lit}`Syntax` adds the
statements. Names are the decoded identifier text, with their case kept; omitted parts
are {lit}`none`. The frontend maps each parser production to one constructor without
reading the schema, and refuses syntax that has no constructor. Numeric literals keep their
token text, because SQLite's conversion rules are not lexical. -/

namespace Belay.Sqlite.Syntax

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
  deriving Repr, DecidableEq

/-- An expression as written. For example, the literal {lit}`-5` is
{lean}`Expr.negate (.numeric "5")`. -/
inductive Expr where
  /-- The {lit}`NULL` keyword. -/
  | null
  /-- A numeric literal's token text, for example {lean}`Expr.numeric "1_000"`. -/
  | numeric (text : String)
  /-- A string literal's decoded UTF-8 bytes, without the quotes. -/
  | string (bytes : List UInt8)
  /-- A blob literal's decoded bytes, for example {lit}`X'00FF'` gives two bytes. -/
  | blob (bytes : List UInt8)
  /-- The keywords {lit}`CURRENT_TIME`, {lit}`CURRENT_DATE` or
  {lit}`CURRENT_TIMESTAMP`, as written. -/
  | currentTime (keyword : String)
  /-- An identifier with how it was quoted ({name}`QuoteKind`), which decides SQLite's
  double-quoted-string fallback and whether {lit}`TRUE` and {lit}`FALSE` are keywords. -/
  | identifier (name : Identifier) (quote : QuoteKind)
  /-- A qualified column name {lit}`source.column`, with both names as written. The
  source is a table name or an alias. -/
  | qualified (source column : Identifier)
  /-- Unary minus. -/
  | negate (operand : Expr)
  /-- Unary plus, which SQLite keeps as a no-op. -/
  | positive (operand : Expr)
  /-- A comparison: {lit}`=` or {lit}`==`, {lit}`<>`, {lit}`<`, {lit}`<=`, {lit}`>`,
  {lit}`>=`, {lit}`IS` or {lit}`IS NOT`. -/
  | compare (operator : Comparison) (left right : Expr)
  /-- {lit}`AND`. -/
  | and (left right : Expr)
  /-- {lit}`OR`. -/
  | or (left right : Expr)
  /-- {lit}`NOT`. -/
  | not (operand : Expr)
  /-- {lit}`IS NULL`, or {lit}`IS NOT NULL` (also {lit}`NOTNULL`) when {lit}`negated`. -/
  | isNull (operand : Expr) (negated : Bool)
  /-- A function call with {lit}`*` as its argument, such as {lit}`COUNT(*)`, with the
  function name as written. -/
  | callStar (name : String)
  /-- A function call with its arguments in written order, with the function name as
  written; {lit}`date()` has no arguments. The operators {lit}`->` and {lit}`->>` are calls
  of functions with those names, as SQLite's parser makes them. Resolution folds the name
  and decides the function. For example, {lit}`COALESCE(a, b)` is
  {lean}`Expr.call "COALESCE" [.identifier (name! "a") .none, .identifier (name! "b") .none]`. -/
  | call (name : String) (arguments : List Expr)
  /-- An arithmetic operator, {lit}`+`, {lit}`-`, {lit}`*`, {lit}`/` or {lit}`%`, between
  two expressions. -/
  | arithmetic (operator : ArithmeticOperator) (left right : Expr)
  /-- {lit}`CAST(operand AS typeName)`, with the type name as written. -/
  | cast (operand : Expr) (typeName : String)
  /-- {lit}`operand COLLATE name` (ADR 0014, slice 3): the operand's value with the named
  collation, as written. -/
  | collate (operand : Expr) (name : Identifier)
  /-- {lit}`EXISTS (q)` (ADR 0018, D1), where {lit}`q` is subquery {lit}`index` of the
  statement ({lit}`Subquery`); {lit}`NOT EXISTS` is {lit}`NOT` of it, as SQLite parses it. -/
  | exists (index : Nat)
  /-- {lit}`operand IN (q)`, or {lit}`operand NOT IN (q)` when {lit}`negated`, where {lit}`q` is
  subquery {lit}`index` of the statement. -/
  | inQuery (operand : Expr) (index : Nat) (negated : Bool)
  /-- A scalar subquery {lit}`(q)`, where {lit}`q` is subquery {lit}`index` of the statement. -/
  | subquery (index : Nat)
  deriving Repr, BEq, Inhabited

/-- One result column of a {lit}`SELECT`: {lit}`*`, or an expression with an
optional {lit}`AS` alias and its source text as written, which SQLite uses as the
column name when there is no alias. -/
inductive ResultColumn where
  /-- {lit}`*`: every column of every source. -/
  | star
  /-- {lit}`source.*`: every column of the source with this name, as written. -/
  | sourceStar (source : Identifier)
  /-- An expression, its alias, and its source text. -/
  | expression (value : Expr) (alias : Option Identifier) (text : String)
  deriving Repr, BEq

/-- A table in {lit}`FROM`, or a table-valued function such as {lit}`json_each(json)`: its
name and its optional alias, both as written, and the arguments of a function. Use
{lean}`(none : Option Identifier)` for no alias, and {lean}`(none : Option (List Expr))` for a
table. -/
structure TableReference where
  /-- The table name, or the function name. -/
  table : Identifier
  /-- The alias of {lit}`table AS alias` or {lit}`table alias`. -/
  alias : Option Identifier
  /-- The arguments of a table-valued function in written order; none for a table. -/
  arguments : Option (List Expr) := none
  deriving Repr, BEq

/-- One join of {lit}`FROM` after the first table: the keywords of its operator, the
joined table, its optional {lit}`ON` condition and its optional {lit}`USING` column
names. For {lit}`, t` the operator has no keywords and all optional parts are absent. -/
structure Join where
  /-- The keywords of the join operator before {lit}`JOIN`, as written, such as
  {lean}`["LEFT", "outer"]`; empty for {lit}`,` and a plain {lit}`JOIN`. Lean reads the
  kind of the join from them, so the frontend does not fold their case. -/
  operator : List String
  /-- The joined table. -/
  source : TableReference
  /-- The {lit}`ON` condition. -/
  condition : Option Expr
  /-- The {lit}`USING` column names, as written. -/
  usingColumns : Option (List Identifier)
  deriving Repr, BEq

/-- One {lit}`ORDER BY` term: an expression, and whether it is {lit}`DESC`. -/
structure OrderTerm where
  /-- The term as written. -/
  expression : Expr
  /-- Whether the term is {lit}`DESC`; {lean}`false` for {lit}`ASC` or no direction. -/
  descending : Bool
  deriving Repr, BEq

/-- A subquery of a statement as written (ADR 0018, D1): its clauses, as those of
{lit}`Syntax.Statement.select`, and the query around it, an earlier subquery by its index in
the statement's list or {lean}`(none : Option Nat)` for the statement's query. The frontend
lists the subqueries in the order of their text, so a subquery comes after the query around
it; an expression names a subquery by its index ({lit}`Expr.exists`, {lit}`Expr.inQuery`,
{lit}`Expr.subquery`). -/
structure Subquery where
  /-- The result columns. -/
  columns : List ResultColumn
  /-- The first table of {lit}`FROM`, or none without {lit}`FROM`. -/
  source : Option TableReference
  /-- The joins after the first table, in order. -/
  joins : List Join
  /-- The {lit}`WHERE` condition. -/
  filter : Option Expr
  /-- The {lit}`GROUP BY` terms. -/
  groupBy : List Expr
  /-- The {lit}`ORDER BY` terms. -/
  orderBy : List OrderTerm
  /-- The {lit}`LIMIT` expression. -/
  limit : Option Expr
  /-- The {lit}`OFFSET` expression. -/
  offset : Option Expr
  /-- The index of the subquery around this one, or none for the statement's query. -/
  parent : Option Nat
  deriving Repr, BEq

end Belay.Sqlite.Syntax
