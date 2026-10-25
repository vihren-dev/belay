import Belay.Sqlite.Model.Resolution.ColumnTypeNames

set_option doc.verso true

/-! Expression affinity and possible storage classes used to derive source
column metadata. These follow SQLite's expression rules before evaluation. -/

namespace Belay.Sqlite.Model

/-- SQLite's numeric and text possibility bits for a result expression. Blob and NULL
possibilities cannot change compound-column affinity and need no bit here. -/
abbrev ExpressionTypes := Bool × Bool

/-- Combine the numeric and text possibilities of two expressions. -/
def ExpressionTypes.union (left right : ExpressionTypes) : ExpressionTypes :=
  (left.1 || right.1, left.2 || right.2)

/-- Possibilities for a column, scalar subquery or CAST from its affinity. -/
def affinityTypes (affinity : Option Affinity) : ExpressionTypes :=
  if affinity.any numericAffinity then (true, false)
  else if affinity == some .text then (false, true) else (true, true)

/-- The affinity of a successfully resolved expression. Only a column, CAST, scalar subquery,
or COLLATE around one has affinity; unary plus removes it. Unknown names have none. -/
def Syntax.Expr.sourceAffinity (scope : Scope) (shapes : SubqueryShapes) : Syntax.Expr → Option Affinity
  | .identifier name _ => match scope.resolveName name with
    | .found _ reads => (scope.nameOperand reads).2
    | .missing | .ambiguous => none
  | .qualified source column schema => match scope.resolveSchemaQualified source column schema with
    | .found _ reads => (scope.nameOperand reads).2
    | .missing | .ambiguous => none
  | .cast _ typeName => some (affinityOf (some typeName))
  | .collate operand _ => operand.sourceAffinity scope shapes
  | .subquery index => (shapes.find index).bind (·.affinity)
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .exists _ | .inQuery .. | .inList .. | .between .. | .caseOf .. | .concatenate .. | .raise .. => none

mutual
/-- SQLite's numeric and text possibility bits ({lit}`sqlite3ExprDataType`) after names
resolve. CASE combines its result arms; unary plus retains type possibilities while removing
affinity. A missing double-quoted identifier has become a string, and TRUE/FALSE a number. -/
def Syntax.Expr.sourceTypes (scope : Scope) (shapes : SubqueryShapes) : Syntax.Expr → ExpressionTypes
  | .null | .blob _ => (false, false)
  | .string _ | .concatenate .. => (false, true)
  | .collate operand _ | .positive operand => operand.sourceTypes scope shapes
  | .parameter _ | .call .. | .callStar _ | .currentTime _ => (true, true)
  | value@(.identifier name quote) =>
    match scope.resolveName name with
    | .found .. => affinityTypes (value.sourceAffinity scope shapes)
    | .missing | .ambiguous => if quote == .double then (false, true) else (true, false)
  | value@(.qualified source column schema) =>
    match scope.resolveSchemaQualified source column schema with
    | .found _ reads => if reads.any scope.triggerCell then (true, false)
      else affinityTypes (value.sourceAffinity scope shapes)
    | .missing | .ambiguous => (true, true)
  | value@(.subquery _) | value@(.cast ..) => affinityTypes (value.sourceAffinity scope shapes)
  | .caseOf operands hasBase =>
    let types := Syntax.Expr.sourceTypesList scope shapes operands
    let arms := if hasBase then types.drop 1 else types
    arms.zipIdx.foldl (fun types (arm, index) =>
      if index % 2 == 1 || index + 1 == arms.length then
        ExpressionTypes.union types arm else types) (false, false)
  | .numeric _ | .negate _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .exists _ | .inQuery .. | .inList .. | .between .. | .raise .. => (true, false)

/-- Type possibilities of each expression, used for the result arms of CASE. -/
def Syntax.Expr.sourceTypesList (scope : Scope) (shapes : SubqueryShapes) : List Syntax.Expr → List ExpressionTypes
  | [] => []
  | first :: rest => first.sourceTypes scope shapes :: Syntax.Expr.sourceTypesList scope shapes rest
end

end Belay.Sqlite.Model
