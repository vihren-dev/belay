import Belay.Sqlite.Model.Queries.Select.CommonTableResolutionExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.NameTraceStatementExamples

/-- The identifier of a text. -/
def name (text : String) : Identifier := Identifier.ofString text

/-- An unqualified column name. -/
def column (text : String) : Syntax.Expr := .identifier (name text) .none

/-- A table reference without an alias. -/
def from_ (text : String) : Option Syntax.TableReference := some { table := name text, alias := none }

/-- A query of the table {lit}`source` with one result column {lit}`a` and the given filter. -/
def query (source : String) (filter : Option Syntax.Expr := none) : Syntax.Subquery :=
  { columns := [.expression (column "a") none "a"], source := from_ source, joins := [], filter := filter,
    groupBy := [], orderBy := [], limit := none, offset := none, parent := none }

/-- The catalog of the examples. -/
def catalog : Catalog :=
  [{ name := name "t", entry := .table { columns := [{ name := name "a", declaredType := some "INTEGER" },
      { name := name "b", declaredType := some "TEXT" }], primaryKey := [0], uniqueKeys := [[1]] } },
   { name := name "v", entry := .view { query := query "t" } }]

/-- A SELECT of the given result column from a table, with WITH definitions. -/
def select (result : Syntax.Expr) (source : String) (filter : Option Syntax.Expr := none)
    (definitions : List Syntax.Subquery := []) : Syntax.Statement :=
  .select [.expression result none "r"] (from_ source) [] filter [] [] none none definitions

/-- The result of the first occurrence at a path with a role. -/
def resultAt (trace : NameTrace) (path : List Nat) (role : NameRole) : Option NameResult :=
  (trace.find? fun occurrence => occurrence.path == path && occurrence.role == role).map (·.result)

/-- The facts of a name that one column binds. -/
structure Bound where
  /-- The kind of the source. -/
  kind : SourceKind
  /-- The catalog position of the source. -/
  position : Option Nat
  /-- How many queries out the source is. -/
  depth : Nat
  /-- The constraints of a declared column. -/
  constraints : Option ColumnConstraints
  deriving DecidableEq

/-- The facts of a result that binds exactly one column. -/
def boundTo : Option NameResult → Option Bound
  | some (.found [binding]) =>
    let constraints := match binding.column.origin with
      | .declared constraints => some constraints
      | .inferred _ => none
    some { kind := binding.source.kind, position := binding.source.position, depth := binding.source.depth,
           constraints := constraints }
  | some (.found _) | some (.ambiguous _) | some (.missing ..) | some (.source _) | some (.schema _)
  | some (.resultColumn _) | some .declares | some (.compared ..) | some (.unreached _) | none => none

/-- The kind, catalog position and view or definition index of a result that is a source. -/
def sourceOf : Option NameResult → Option (SourceKind × Option Nat × Option Nat)
  | some (.source reference) => some (reference.kind, reference.position, reference.query)
  | some (.found _) | some (.ambiguous _) | some (.missing ..) | some (.schema _) | some (.resultColumn _)
  | some .declares | some (.compared ..) | some (.unreached _) | none => none

/-- The names of the candidates of a name that is an error because it is missing. -/
def missingNames : Option NameResult → Option (List Identifier)
  | some (.missing .error candidates) => some (candidates.map fun
      | .column binding => binding.column.name
      | .resultAlias alias _ => alias
      | .source reference => reference.name
      | .catalogObject _ objectName _ => objectName)
  | some (.missing .textLiteral _) | some (.missing .booleanKeyword _) | some (.missing .rowidName _)
  | some (.found _) | some (.ambiguous _) | some (.source _) | some (.schema _) | some (.resultColumn _)
  | some .declares | some (.compared ..) | some (.unreached _) | none => none

/-- The affinity and collation of a comparison. -/
def comparedWith : Option NameResult → Option (Option Affinity × Collation)
  | some (.compared _ affinity collation) => some (affinity, collation)
  | some (.found _) | some (.ambiguous _) | some (.missing ..) | some (.source _) | some (.schema _)
  | some (.resultColumn _) | some .declares | some (.unreached _) | none => none

/-- Whether a resolution succeeds. -/
def succeeds {α : Type} : Except NodeRestriction α → Bool
  | .ok _ => true
  | .error _ => false

/-- The path of the node where a resolution is refused, or none when it works. -/
def refusedAt {α : Type} : Except NodeRestriction α → Option (List Nat)
  | .ok _ => none
  | .error restriction => some restriction.path

/-- The filter {lit}`b = 1`. -/
def filterOnB : Syntax.Expr := .compare .eq (column "b") (.numeric "1")

/-- Whether a result is an ambiguous name. -/
def isAmbiguous : Option NameResult → Bool
  | some (.ambiguous _) => true
  | some (.found _) | some (.missing ..) | some (.source _) | some (.schema _) | some (.resultColumn _)
  | some .declares | some (.compared ..) | some (.unreached _) | none => false

/-- The table {lit}`t` joined to the view {lit}`v`, which both have a column {lit}`a`, with the given join
operator. -/
def joinWith (operator : List String) : Syntax.Statement :=
  .select [.expression (column "a") none "a"] (from_ "t")
    [{ operator := operator, source := { table := name "v", alias := none }, condition := none,
       usingColumns := none }] none [] [] none none

end Belay.Sqlite.Model.NameTraceStatementExamples
