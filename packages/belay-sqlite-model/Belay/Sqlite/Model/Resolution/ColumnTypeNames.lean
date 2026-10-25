import Belay.Sqlite.Model.Resolution.ColumnOrigins

set_option doc.verso true

/-! Normalized column declarations for query sources. SQLite retains a column's
written declaration only when its affinity matches. FLEXNUM uses the spelling
{lit}`NUM` even when an underlying declaration has ordinary NUMERIC affinity. -/

namespace Belay.Sqlite.Model

/-- SQLite's normalized declaration for the effective expression affinity.
No affinity has no declaration; a numeric expression uses {lit}`NUM`. -/
def normalizedTypeName : Option Affinity → Option String
  | none => none
  | some .blob => some "BLOB"
  | some .text => some "TEXT"
  | some .integer => some "INT"
  | some .real => some "REAL"
  | some .numeric => some "NUM"

/-- The declaration of a query-source column. Retain the expression's origin
when its affinity matches; otherwise use SQLite's normalized spelling. A
FLEXNUM expression always uses {lit}`NUM`. -/
def queryColumnType (affinity : Option Affinity) (flexibleNumeric : Bool)
    (origin : Option String) : Option String :=
  if flexibleNumeric then some "NUM"
  else if origin.any (fun value => affinity == some (affinityOf (some value))) then origin
  else normalizedTypeName affinity

/-- Whether a name selects a single cell with FLEXNUM metadata. A merged
coalesce, missing name or ambiguous name has no such affinity. -/
def Scope.nameFlexibleNumeric (scope : Scope) : NameResolution → Bool
  | .found _ [position] => !scope.triggerCell position && scope.flexibleNumericAt position
  | .found _ _ | .missing | .ambiguous => false

/-- In the scope of one physical table, every name resolution has ordinary
affinity metadata. Proof sketch: the table supplies no FLEXNUM flags. -/
theorem Scope.nameFlexibleNumeric_single (name : Identifier) (columns : List CatalogColumn)
    (hasRowid : Bool) (resolution : NameResolution) :
    (Scope.single name columns hasRowid).nameFlexibleNumeric resolution = false := by
  unfold Scope.nameFlexibleNumeric
  split <;> simp [Scope.flexibleNumericAt, Scope.single]

/-- FLEXNUM metadata inherited from a column or scalar query. COLLATE keeps
the operand's affinity. CAST and unary plus do not inherit this flag. -/
def Syntax.Expr.flexibleNumeric (scope : Scope) (shapes : SubqueryShapes) : Syntax.Expr → Bool
  | .identifier name _ => scope.nameFlexibleNumeric (scope.resolveName name)
  | .qualified source column schema => scope.nameFlexibleNumeric (scope.resolveSchemaQualified source column schema)
  | .subquery index => (shapes.find index).any (·.flexibleNumeric)
  | .collate operand _ => operand.flexibleNumeric scope shapes
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .exists _ | .inQuery .. | .inList .. | .between .. | .caseOf ..
  | .concatenate .. | .raise .. => false

/-- Every expression in a physical table scope with no resolved subqueries
has ordinary affinity metadata. Proof sketch: names have no FLEXNUM flag,
subquery lookup is empty, and COLLATE preserves the induction hypothesis. -/
theorem Syntax.Expr.flexibleNumeric_single (name : Identifier) (columns : List CatalogColumn)
    (hasRowid : Bool) (current : Option Nat) (value : Syntax.Expr) :
    value.flexibleNumeric (Scope.single name columns hasRowid) { current } = false := by
  fun_induction Syntax.Expr.flexibleNumeric (Scope.single name columns hasRowid) { current } value <;>
    simp_all [Scope.nameFlexibleNumeric_single,
      SubqueryShapes.find, SubqueryShapes.base]

/-- Whether a result expression is a CAST at its root, which can give a
compound column FLEXNUM metadata. Wrapping the CAST in COLLATE changes this. -/
def Syntax.Expr.isRootCast : Syntax.Expr → Bool
  | .cast .. => true
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .collate .. | .exists _ | .inQuery .. | .inList .. | .between .. | .caseOf ..
  | .concatenate .. | .raise .. | .identifier .. | .qualified .. | .subquery _ => false

/-- FLEXNUM metadata of each output column, including star expansion. Use the
first flag for a scalar query; a result without columns supplies no flags. -/
def resultFlexibleNumerics (scope : Scope) (shapes : SubqueryShapes)
    (results : List Syntax.ResultColumn) : List Bool :=
  results.flatMap fun
    | .star => scope.visible.map fun (position, column) =>
      (scope.starColumnIndex position column).any scope.flexibleNumericAt
    | .sourceStar name => ((scope.starColumns? name).getD []).map fun (position, column) =>
      (scope.starColumnIndex position column).any scope.flexibleNumericAt
    | .expression value _ _ => [value.flexibleNumeric scope shapes]

end Belay.Sqlite.Model
