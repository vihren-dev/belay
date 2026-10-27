import Belay.Sqlite.Model.Resolution.RewriteEdit

set_option doc.verso true

/-! Replace one name of an expression by its node path (ADR 0019, D4). The paths are those of the
name trace ({lit}`resolveOperandTraced`): the operand of a unary form is the child 0; the sides of a
comparison or of arithmetic are the children 1 and 2; the sides of {lit}`AND`, {lit}`OR` and {lit}`||`
the children 0 and 1; {lit}`BETWEEN` has its three operands at 0, 1 and 2; the arguments of a call are
below the child 1; the operand of {lit}`IN` is the child 0 and the values of a list below the
child 1; the operands of {lit}`CASE` are below the child 0. In {lit}`source.column`, the source is
the child 0 and the column the child 1. An unqualified name has the path of its node. -/

namespace Belay.Sqlite.Model.Syntax

mutual
/-- The expression with the name at the path replaced, or none when the path leads to no name, or to
a name other than {name}`NameEdit.old`. The quote of an unqualified name follows
{name}`RenameStyle.quote`. -/
def Expr.renameAt (edit : NameEdit) : List Nat → Expr → Option Expr
  | [], .identifier name quote => (edit.replace? name).map fun new => .identifier new (edit.style.quote quote)
  | [0], .qualified source column schema => (edit.replace? source).map fun new => .qualified new column schema
  | [1], .qualified source column schema => (edit.replace? column).map fun new => .qualified source new schema
  | 0 :: rest, .negate operand => (operand.renameAt edit rest).map .negate
  | 0 :: rest, .positive operand => (operand.renameAt edit rest).map .positive
  | 0 :: rest, .not operand => (operand.renameAt edit rest).map .not
  | 0 :: rest, .isNull operand negated => (operand.renameAt edit rest).map (.isNull · negated)
  | 0 :: rest, .cast operand typeName => (operand.renameAt edit rest).map (.cast · typeName)
  | 0 :: rest, .collate operand name => (operand.renameAt edit rest).map (.collate · name)
  | 0 :: rest, .inQuery operand index negated => (operand.renameAt edit rest).map (.inQuery · index negated)
  | 0 :: rest, .inList operand values negated => (operand.renameAt edit rest).map (.inList · values negated)
  | 1 :: index :: rest, .inList operand values negated =>
    (Expr.renameListAt edit index rest values).map (.inList operand · negated)
  | 1 :: index :: rest, .call name arguments => (Expr.renameListAt edit index rest arguments).map (.call name)
  | 0 :: index :: rest, .caseOf operands hasBase => (Expr.renameListAt edit index rest operands).map (.caseOf · hasBase)
  | 1 :: rest, .compare operator left right => (left.renameAt edit rest).map (.compare operator · right)
  | 2 :: rest, .compare operator left right => (right.renameAt edit rest).map (.compare operator left ·)
  | 1 :: rest, .arithmetic operator left right => (left.renameAt edit rest).map (.arithmetic operator · right)
  | 2 :: rest, .arithmetic operator left right => (right.renameAt edit rest).map (.arithmetic operator left ·)
  | 0 :: rest, .and left right => (left.renameAt edit rest).map (.and · right)
  | 1 :: rest, .and left right => (right.renameAt edit rest).map (.and left ·)
  | 0 :: rest, .or left right => (left.renameAt edit rest).map (.or · right)
  | 1 :: rest, .or left right => (right.renameAt edit rest).map (.or left ·)
  | 0 :: rest, .concatenate left right => (left.renameAt edit rest).map (.concatenate · right)
  | 1 :: rest, .concatenate left right => (right.renameAt edit rest).map (.concatenate left ·)
  | 0 :: rest, .between operand low high negated => (operand.renameAt edit rest).map (.between · low high negated)
  | 1 :: rest, .between operand low high negated => (low.renameAt edit rest).map (.between operand · high negated)
  | 2 :: rest, .between operand low high negated => (high.renameAt edit rest).map (.between operand low · negated)
  | _, _ => none

/-- The list with the name at the path inside the element at the index replaced. -/
def Expr.renameListAt (edit : NameEdit) (index : Nat) (rest : List Nat) : List Expr → Option (List Expr)
  | [] => none
  | first :: others => match index with
    | 0 => (first.renameAt edit rest).map (· :: others)
    | index + 1 => (Expr.renameListAt edit index rest others).map (first :: ·)
end

end Belay.Sqlite.Model.Syntax
