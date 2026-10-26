import Belay.Sqlite.Model.Resolution.ExpressionTypes

set_option doc.verso true

/-! Column metadata for query sources (ADR 0019, D5). SQLite's
{lit}`sqlite3SubqueryColumnTypes` uses every result expression, not only the first column
metadata that scalar and IN subqueries need. Affinity belongs to the expression; a literal
has no affinity, which differs from a catalog column declared without a type. -/

namespace Belay.Sqlite.Model

/-- One result column used as a query-source column: name, expression affinity, collation,
type possibilities, and declared-type metadata. Use no affinity for a literal,
BINARY without COLLATE, and omit origin metadata for a result with no declared column. -/
structure DerivedColumn where
  /-- The unique derived-table column name. -/
  name : String
  /-- The expression affinity, including none for a literal. -/
  affinity : Option Affinity
  /-- The expression's collation, BINARY when it has none. -/
  collation : Collation
  /-- The numeric and text possibility bits used to combine compound terms. -/
  types : ExpressionTypes
  /-- The declaration behind this output expression, used when another query
  reads it. A compound follows its right-most term. Omit it for a literal. -/
  originType : Option String := none
  /-- Whether the affinity has SQLite's FLEXNUM metadata. False for ordinary
  expressions; it forces the normalized declaration to {lit}`NUM`. -/
  flexibleNumeric : Bool := false
  /-- Whether the written expression is a CAST at its root. False for a star
  column; a compound uses its first term's flag to select FLEXNUM. -/
  castResult : Bool := false
  /-- The normalized declaration of this source column. Its default follows
  the affinity and origin; a compound recomputes it from its first term. -/
  declaredType : Option String := queryColumnType affinity flexibleNumeric originType
  deriving Repr, DecidableEq

/-- The metadata of successfully resolved result columns, with their original output names.
A merged star column uses the same operand affinity as a written name. -/
def resultSourceColumns (scope : Scope) (shapes : SubqueryShapes) (results : List Syntax.ResultColumn)
    (names : List String) : List DerivedColumn :=
  let starColumn := fun position column =>
    let affinity := match scope.starOperand position column with
      | .ok operand => operand.2
      | .error _ => none
    ({ name := "", affinity, collation := (scope.starCollation position column).getD .binary,
       types := affinityTypes affinity, originType := scope.starOriginType position column,
       flexibleNumeric := (scope.starColumnIndex position column).any scope.flexibleNumericAt } : DerivedColumn)
  let metadata := results.flatMap fun
    | .star => scope.visible.map fun (position, column) => starColumn position column
    | .sourceStar source => ((scope.starColumns? source).getD []).map fun (position, column) =>
      starColumn position column
    | .expression value _ _ =>
      [{ name := "", affinity := value.sourceAffinity scope shapes, collation := value.collationIn scope,
         types := value.sourceTypes scope shapes, originType := value.originType scope shapes,
         flexibleNumeric := value.flexibleNumeric scope shapes, castResult := value.isRootCast }]
  (names.zip metadata).map fun (name, column) => { column with name }

/-- Unique names for the columns of a query source. None means SQLite would choose a random
suffix for a duplicate, outside the deterministic name rules of {name}`derivedNames`. -/
def nameSourceColumns (scope : Scope) (results : List Syntax.ResultColumn)
    (columns : List DerivedColumn) : Option (List DerivedColumn) := do
  let names ← derivedNames scope results (columns.map (·.name))
  pure ((columns.zip names).map fun (column, name) => { column with name })

/-- The affinity of one compound-source column. SQLite takes the first expression with an
affinity, then changes TEXT to BLOB if another term may be numeric, or numeric affinity to
BLOB if another term may be text. No expression with affinity gives none. -/
def compoundSourceAffinity (columns : List DerivedColumn) : Option Affinity :=
  let selected := columns.findIdx? (·.affinity.isSome)
  selected.bind fun index => do
    let affinity ← columns[index]?.bind (·.affinity)
    let others := (columns.take index ++ columns.drop (index + 1)).foldl
      (fun types column => ExpressionTypes.union types column.types) (false, false)
    pure (if affinity == .text && others.1 || numericAffinity affinity && others.2 then .blob else affinity)

/-- Combine all output columns of compound terms. Names, collations and type possibilities
come from the left-most term; affinity follows {name}`compoundSourceAffinity` for each column.
An enclosing expression follows the right-most declared-type origin. The source
column's own declaration instead uses the left-most origin and effective affinity.
A retained numeric affinity from a first-term CAST is FLEXNUM for a compound. -/
def compoundSourceColumns (terms : List (List DerivedColumn)) : List DerivedColumn :=
  ((terms.head?).getD []).mapIdx fun index first =>
    let columns := terms.filterMap (·[index]?)
    let affinity := compoundSourceAffinity columns
    let flexibleNumeric := affinity.any numericAffinity &&
      (columns.find? (·.affinity.isSome)).any (·.flexibleNumeric) ||
      affinity.any numericAffinity && first.castResult && columns.length > 1
    { first with
      affinity := affinity, flexibleNumeric := flexibleNumeric,
      originType := columns.getLast?.bind (·.originType),
      declaredType := queryColumnType affinity flexibleNumeric first.originType }

/-- The scope metadata of an indexed query source. An omitted alias gives unqualified
columns only; a source never has an implicit rowid. Normalized declarations,
expression origins, affinities and FLEXNUM flags each retain their own meaning. -/
def derivedScopeSource (index : Nat) (alias : Option Identifier) (columns : List DerivedColumn) : ScopeSource :=
  { name := alias.getD (name! ""), qualified := alias.isSome, queryIndex := some index, hasRowid := false,
    role := .derivedTable,
    columns := columns.map fun column =>
      { name := Identifier.ofString column.name, declaredType := column.declaredType, collation := column.collation },
    affinities := some (columns.map (·.affinity)),
    originTypes := some (columns.map (·.originType)), flexibleNumeric := columns.map (·.flexibleNumeric) }

end Belay.Sqlite.Model
