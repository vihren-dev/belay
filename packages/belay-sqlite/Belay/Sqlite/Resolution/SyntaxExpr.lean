import Belay.Sqlite.Declarations
import Belay.Sqlite.Operators
import Belay.Sqlite.Resolution.ConflictAlgorithm

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
  | identifier (name : String) (quote : QuoteKind)
  /-- A qualified column name {lit}`source.column`, with both names as written. The
  source is a table name or an alias. -/
  | qualified (source column : String)
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
  {lean}`Expr.call "COALESCE" [.identifier "a" .none, .identifier "b" .none]`. -/
  | call (name : String) (arguments : List Expr)
  /-- An arithmetic operator, {lit}`+`, {lit}`-`, {lit}`*`, {lit}`/` or {lit}`%`, between
  two expressions. -/
  | arithmetic (operator : ArithmeticOperator) (left right : Expr)
  /-- {lit}`CAST(operand AS typeName)`, with the type name as written. -/
  | cast (operand : Expr) (typeName : String)
  deriving Repr, BEq, Inhabited

/-- A DEFAULT expression and its source spelling. The expression determines the
value; the text preserves metadata such as {lit}`X'00ff'` versus {lit}`x'00FF'`.
For example, {lean}`({ expression := .numeric "7", sourceText := "7" } : DefaultExpression)`
is the default written as {lit}`7`. -/
structure DefaultExpression where
  /-- The expression evaluated when a column value is omitted. -/
  expression : Expr
  /-- The expression text reported by SQLite, excluding DEFAULT and its outer parentheses. -/
  sourceText : String
  deriving BEq

/-- Print a default as a constructor application so generated nested catalog terms
keep valid Lean indentation when an expression spans several lines. -/
instance : Repr DefaultExpression where
  reprPrec value prec := Repr.addAppParen
    ("Belay.Sqlite.Syntax.DefaultExpression.mk " ++ reprArg value.expression ++ " " ++ reprArg value.sourceText) prec

/-- A column constraint as written. For example, {lit}`PRIMARY KEY DESC` is
{lean}`ColumnConstraint.primaryKey true`. -/
inductive ColumnConstraint where
  /-- {lit}`NOT NULL [ON CONFLICT algorithm]`; {lean}`(none : Option ConflictAlgorithm)`
  without the clause. -/
  | notNull (algorithm : Option ConflictAlgorithm := none)
  /-- {lit}`PRIMARY KEY [ASC | DESC] [ON CONFLICT algorithm]`; the flag is true for
  {lit}`DESC`. -/
  | primaryKey (descending : Bool) (algorithm : Option ConflictAlgorithm := none)
  /-- {lit}`UNIQUE [ON CONFLICT algorithm]`. -/
  | unique (algorithm : Option ConflictAlgorithm := none)
  /-- {lit}`DEFAULT` with its expression and its source text, excluding DEFAULT
  and any outer parentheses belonging to the DEFAULT production. -/
  | default (value : Expr) (sourceText : String)
  deriving Repr, BEq

/-- One column of CREATE TABLE or ADD COLUMN. Use {lean}`(none : Option String)`
for a column without a declared type. -/
structure ColumnDefinition where
  /-- The column name as written. -/
  name : String
  /-- The declared type text as written, for example {lit}`VARCHAR(10)`. -/
  declaredType : Option String
  /-- The column constraints in written order. -/
  constraints : List ColumnConstraint
  deriving Repr, BEq

/-- A table constraint of CREATE TABLE, with column names as written. -/
inductive TableConstraint where
  /-- {lit}`PRIMARY KEY (columns) [ON CONFLICT algorithm]`. -/
  | primaryKey (columns : List String) (algorithm : Option ConflictAlgorithm := none)
  /-- {lit}`UNIQUE (columns) [ON CONFLICT algorithm]`. -/
  | unique (columns : List String) (algorithm : Option ConflictAlgorithm := none)
  deriving Repr, BEq

/-- One result column of a {lit}`SELECT`: {lit}`*`, or an expression with an
optional {lit}`AS` alias and its source text as written, which SQLite uses as the
column name when there is no alias. -/
inductive ResultColumn where
  /-- {lit}`*`: every column of every source. -/
  | star
  /-- {lit}`source.*`: every column of the source with this name, as written. -/
  | sourceStar (source : String)
  /-- An expression, its alias, and its source text. -/
  | expression (value : Expr) (alias : Option String) (text : String)
  deriving Repr, BEq

/-- A table in {lit}`FROM`, or a table-valued function such as {lit}`json_each(json)`: its
name and its optional alias, both as written, and the arguments of a function. Use
{lean}`(none : Option String)` for no alias, and {lean}`(none : Option (List Expr))` for a
table. -/
structure TableReference where
  /-- The table name, or the function name. -/
  table : String
  /-- The alias of {lit}`table AS alias` or {lit}`table alias`. -/
  alias : Option String
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
  usingColumns : Option (List String)
  deriving Repr, BEq

/-- One {lit}`ORDER BY` term: an expression, and whether it is {lit}`DESC`. -/
structure OrderTerm where
  /-- The term as written. -/
  expression : Expr
  /-- Whether the term is {lit}`DESC`; {lean}`false` for {lit}`ASC` or no direction. -/
  descending : Bool
  deriving Repr, BEq

end Belay.Sqlite.Syntax
