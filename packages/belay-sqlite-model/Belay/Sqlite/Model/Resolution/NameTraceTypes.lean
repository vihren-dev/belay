import Belay.Sqlite.Model.Resolution.Scope
import Belay.Sqlite.Model.Resolution.SyntaxExpr

set_option doc.verso true

/-! The data types of the name trace: for each name of a statement, what the model's resolver
decided. A client such as the editor reads the trace to describe a name; the trace changes no
resolved statement. A trace lists the occurrences in the order in which the resolver reaches them. -/

namespace Belay.Sqlite.Model

/-- What kind of object a source of a scope is. -/
inductive SourceKind where
  /-- A table of the catalog. -/
  | baseTable
  /-- A table of the fixed initial database of a two-state query, written {lit}`before.t`. -/
  | initialTable
  /-- A stored view of the catalog. -/
  | storedView
  /-- A {lit}`WITH` definition of the statement. -/
  | commonTable
  /-- A subquery in {lit}`FROM`. -/
  | derivedTable
  /-- A table-valued function such as {lit}`json_each`, or a table-valued pragma. -/
  | tableFunction
  /-- The row that an upsert proposed, named {lit}`excluded`. -/
  | proposedRow
  /-- The {lit}`NEW` or {lit}`OLD` row of a trigger. -/
  | triggerRow
  deriving Repr, DecidableEq

/-- One source of a scope as a name sees it. -/
structure SourceRef where
  /-- What the source is. -/
  kind : SourceKind
  /-- The name that qualifies its columns: the alias as written, else the table name as declared. -/
  name : Identifier
  /-- The position of the source in the scope, counted from the outermost query. -/
  index : Nat
  /-- How many queries out the source is: 0 for a source of the query that holds the name. -/
  depth : Nat
  /-- The catalog position of a table or view; none for any other source. -/
  position : Option Nat := none
  /-- The index of the query that supplies a view, a {lit}`WITH` definition or a derived table. -/
  query : Option Nat := none
  deriving Repr, DecidableEq

/-- The constraints of a column of a catalog table. -/
structure ColumnConstraints where
  /-- Whether the column is part of the primary key. -/
  primaryKey : Bool
  /-- Whether the column is part of a UNIQUE constraint. -/
  unique : Bool
  /-- Whether the column is part of a foreign key of its table. -/
  foreignKey : Bool
  /-- Whether the column declares NOT NULL. -/
  notNull : Bool
  deriving Repr, DecidableEq

/-- Where the facts of a bound column come from. -/
inductive ColumnOrigin where
  /-- A column that a catalog table declares, with its constraints. -/
  | declared (constraints : ColumnConstraints)
  /-- A column of a derived table, view or {lit}`WITH` definition; the declared type is followed. -/
  | inferred (originType : Option String)
  deriving Repr, DecidableEq

/-- A column that a name binds. -/
structure BoundColumn where
  /-- The position of the column in the joined row of the scope. -/
  position : Nat
  /-- The position of the column in its source. -/
  index : Nat
  /-- The name of the column in its source. -/
  name : Identifier
  /-- The declared type text in its source, or none ({name}`ColumnOrigin.inferred`). -/
  declaredType : Option String
  /-- The affinity that a comparison uses for the column; none for an expression without one. -/
  affinity : Option Affinity
  /-- The collation of the column. -/
  collation : Collation
  /-- Where these facts come from. -/
  origin : ColumnOrigin
  deriving Repr, DecidableEq

/-- A source with one of its columns. -/
structure Binding where
  /-- The source. -/
  source : SourceRef
  /-- The column. -/
  column : BoundColumn
  deriving Repr, DecidableEq

/-- Something that a missing or ambiguous name may stand for, with its scope source. -/
inductive Candidate where
  /-- A column of a source that is in scope. -/
  | column (binding : Binding)
  /-- The alias of a result column of the query, legal where result aliases are. -/
  | resultAlias (name : Identifier) (resultColumn : Nat)
  /-- A source that a qualifier or a table reference could name. -/
  | source (source : SourceRef)
  deriving Repr, DecidableEq

/-- What the resolver made of a name that no column of the scope has. -/
inductive MissingUse where
  /-- SQLite's {lit}`no such column`, or {lit}`no such table`. -/
  | error
  /-- A double-quoted name that is a text literal (the double-quoted string fallback). -/
  | textLiteral
  /-- The unquoted keywords {lit}`TRUE` and {lit}`FALSE`, which are integers. -/
  | booleanKeyword
  /-- A rowid name, which the model refuses where a source has a rowid. -/
  | rowidName
  deriving Repr, DecidableEq

/-- The kind of expression that compares two values with an affinity and a collation. -/
inductive ComparisonForm where
  /-- A comparison operator. -/
  | operator (operator : Comparison)
  /-- {lit}`x IN (list)`. -/
  | inList
  /-- {lit}`x IN (query)`. -/
  | inQuery
  /-- The lower bound of {lit}`BETWEEN`. -/
  | betweenLow
  /-- The upper bound of {lit}`BETWEEN`. -/
  | betweenHigh
  /-- A {lit}`WHEN` value of {lit}`CASE` that has a base expression. -/
  | caseWhen
  deriving Repr, DecidableEq

/-- Why a name has no result. -/
inductive Unreached where
  /-- The model refuses the form: a restriction of the model. -/
  | refused
  deriving Repr, DecidableEq

/-- What the resolver decided about one occurrence. -/
inductive NameResult where
  /-- The name is bound: one binding, or several for a column that a join merged. -/
  | found (bindings : List Binding)
  /-- Two columns that no join merged have the name. -/
  | ambiguous (candidates : List Candidate)
  /-- No column has the name; the candidates are the names legal at this place. -/
  | missing (use : MissingUse) (candidates : List Candidate)
  /-- The name is a table reference or a qualifier that resolved to a source. -/
  | source (source : SourceRef)
  /-- The schema of a qualified name; {lit}`known` is true for {lit}`before`. -/
  | schema (known : Bool)
  /-- The name is a result alias that an {lit}`ORDER BY` or {lit}`GROUP BY` term names. -/
  | resultColumn (index : Nat)
  /-- The name declares an alias, a {lit}`WITH` definition or a column name. -/
  | declares
  /-- A comparison with the affinity and the collation that the resolver applied. -/
  | compared (form : ComparisonForm) (affinity : Option Affinity) (collation : Collation)
  /-- The resolver did not look the name up. -/
  | unreached (why : Unreached)
  deriving Repr, DecidableEq

/-- The role of an occurrence. -/
inductive NameRole where
  /-- A table, view or {lit}`WITH` definition named in {lit}`FROM` or a write. -/
  | tableReference
  /-- A column in an expression. -/
  | columnReference
  /-- A column in a column list or an assignment target. -/
  | columnTarget
  /-- The source part of {lit}`source.column`, {lit}`source.*` or {lit}`schema.source.column`. -/
  | qualifier
  /-- A table alias, a derived table alias, or a name that a {lit}`WITH` definition declares. -/
  | aliasDeclaration
  /-- The alias of a result column. -/
  | resultAlias
  /-- A comparison, with no name. -/
  | comparisonSite
  deriving Repr, DecidableEq

/-- One occurrence of a name in a statement. -/
structure NameOccurrence where
  /-- The node path in the statement as written ({lit}`NodeRestriction.path`); for a comparison,
  the path of the comparing expression. -/
  path : List Nat
  /-- Whether the path is the text of the name itself; false for a name inside a stored view, which
  has the use site of the view as its path. -/
  exact : Bool := true
  /-- The role of the occurrence. -/
  role : NameRole
  /-- The name as written; none for a comparison. -/
  name : Option Identifier
  /-- How the name was quoted, when the syntax keeps it: only for an unqualified column name. -/
  quote : Option Syntax.QuoteKind := none
  /-- What the resolver decided. -/
  result : NameResult
  deriving Repr, DecidableEq

/-- The occurrences of a statement, in the order in which the resolver reaches them. -/
abbrev NameTrace := List NameOccurrence

end Belay.Sqlite.Model
