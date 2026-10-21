import Belay.Sqlite.Translation.Expressions
import Belay.Sqlite.Translation.Forms

set_option doc.verso true

/-! The expressions of a query. The port of the expression part of
{lit}`belay/sqlite/syntax_queries.py`: comparisons, connectives, arithmetic, {lit}`IS NULL`,
{lit}`CAST`, qualified names, function calls with the name as written, {lit}`LIKE` and the other
{lit}`likeop` operators as calls, {lit}`->` and {lit}`->>` as calls, {lit}`COLLATE`, {lit}`RAISE`,
and the forms of {lit}`Forms.lean`. Each operand goes through {name}`Belay.Sqlite.Translation.Mappers.expression`. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- The comparison of a comparison token. -/
def comparisonOf : String → Option Comparison
  | "EQ" => some .eq | "NE" => some .ne | "LT" => some .lt | "LE" => some .le | "GT" => some .gt
  | "GE" => some .ge | _ => none

/-- The {lit}`Syntax.Expr` constructor of a logical token. -/
def connectiveOf : String → Option (Syntax.Expr → Syntax.Expr → Syntax.Expr)
  | "AND" => some .and | "OR" => some .or | _ => none

/-- The arithmetic operator of an arithmetic token. -/
def arithmeticOf : String → Option ArithmeticOperator
  | "PLUS" => some .add | "MINUS" => some .subtract | "STAR" => some .multiply | "SLASH" => some .divide
  | "REM" => some .remainder | _ => none

/-- The kind of a {lit}`raisetype` token. -/
def raiseKindOf : String → Syntax.RaiseKind
  | "ROLLBACK" => .rollback | "ABORT" => .abort | _ => .fail

/-- A constructor with an operator and two operands, a comparison or an arithmetic operator; the
operator's range is the expression's. -/
def operation (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (make : Syntax.Expr → Syntax.Expr → Syntax.Expr)
    (left right : ParseNode) : TranslateM (Located Syntax.Expr) := do
  let leftPart ← mappers.expression tree left
  let rightPart ← mappers.expression tree right
  return composite (make leftPart.value rightPart.value) node.start node.stop #[spanOf node, leftPart.span, rightPart.span]

/-- A constructor of one operand. -/
def unary (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (make : Syntax.Expr → Syntax.Expr)
    (operand : ParseNode) : TranslateM (Located Syntax.Expr) := do
  let part ← mappers.expression tree operand
  return composite (make part.value) node.start node.stop #[part.span]

/-- A call of the function with its arguments in written order. -/
def call (mappers : Mappers) (tree : SqlTree) (start stop : Nat) (function : Located String)
    (arguments : Array ParseNode) : TranslateM (Located Syntax.Expr) := do
  let items ← arguments.mapM (mappers.expression tree)
  let listed := sequence items (items[0]?.map (·.span.start) |>.getD stop) (items.back?.map (·.span.stop) |>.getD stop)
  return composite (.call function.value listed.value) start stop #[function.span, listed.span]

/-- A call with {lit}`*`, or with zero or more arguments, with the function name as written. -/
def functionCall (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM (Located Syntax.Expr) := do
  let function ← if parts[0]!.symbol == "ID" then plainName tree parts[0]!
    else pure (leaf (tree.text parts[0]!) parts[0]!.start parts[0]!.stop)
  match (parts.extract 1 parts.size).toList.map (·.symbol) with
  | ["LP", "STAR", "RP"] => return composite (.callStar function.value) node.start node.stop #[function.span]
  | ["LP", "distinct", "exprlist", "RP"] =>
    absent parts[2]! "DISTINCT in a function call"
    call mappers tree node.start node.stop function (← expressionList tree parts[3]!)
  | _ => unsupported node ("A function call with ORDER BY, FILTER or OVER is not modeled; " ++
      "write the call with its arguments only")

/-- {lit}`x LIKE p [ESCAPE e]` and the other {lit}`likeop` operators: a call of the function named
by the operator, with the pattern first, the operand second and the escape last, and
{lit}`not` around it for {lit}`NOT`. -/
def like (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM (Located Syntax.Expr) := do
  let operator := tree.children parts[1]!
  let keyword := operator.back!
  let arguments := #[parts[2]!, parts[0]!] ++ (if parts.size == 5 then #[parts[4]!] else #[])
  let called ← call mappers tree node.start node.stop (leaf (tree.text keyword) keyword.start keyword.stop) arguments
  if tree.symbols parts[1]! == ["NOT", "LIKE_KW"] then
    return composite (.not called.value) node.start node.stop #[called.span]
  return called

/-- The binary forms {lit}`expr OP expr`: comparison, {lit}`IS`, connective and arithmetic. -/
def binaryForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) (symbol : String) :
    Option (TranslateM (Located Syntax.Expr)) :=
  match comparisonOf symbol, connectiveOf symbol, arithmeticOf symbol with
  | some operator, _, _ => some (operation mappers tree node (.compare operator) parts[0]! parts[2]!)
  | none, some make, _ => some do
    let left ← mappers.expression tree parts[0]!
    let right ← mappers.expression tree parts[2]!
    return composite (make left.value right.value) node.start node.stop #[left.span, right.span]
  | none, none, some operator => some (operation mappers tree node (.arithmetic operator) parts[0]! parts[2]!)
  | none, none, none =>
    if symbol == "IS" then some (operation mappers tree node (.compare .is) parts[0]! parts[2]!) else none

/-- {lit}`RAISE(IGNORE)` and {lit}`RAISE(kind, message)`. -/
def raiseForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) (ignore : Bool) :
    TranslateM (Located Syntax.Expr) := do
  if ignore then
    return composite (.raise .ignore none) node.start node.stop #[spanOf parts[2]!, spanOf node]
  let kind := (tree.children parts[2]!)[0]!
  let message ← mappers.expression tree parts[4]!
  return composite (.raise (raiseKindOf kind.symbol) (some message.value)) node.start node.stop
    #[spanOf kind, message.span]

end Belay.Sqlite.Translation
