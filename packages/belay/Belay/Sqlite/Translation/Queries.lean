import Belay.Sqlite.Translation.Expressions
import Belay.Sqlite.Translation.Forms

set_option doc.verso true

/-! The expressions of a query. The port of the expression part of
{lit}`belay/sqlite/syntax_queries.py`: comparisons, connectives, arithmetic, {lit}`IS NULL`,
{lit}`CAST`, qualified names, function calls with the name as written, {lit}`LIKE` and the other
{lit}`likeop` operators as calls, {lit}`->` and {lit}`->>` as calls, {lit}`COLLATE`, {lit}`RAISE`,
and the forms of {lit}`Forms.lean`. Each operand goes through {name}`Belay.Sqlite.Translation.Mappers.expression`. -/

namespace Belay.Sqlite.Translation

/-- The {lit}`Comparison` constructor of a comparison token. -/
def comparisonOf : String → Option String
  | "EQ" => some "eq" | "NE" => some "ne" | "LT" => some "lt" | "LE" => some "le" | "GT" => some "gt"
  | "GE" => some "ge" | _ => none

/-- The {lit}`Syntax.Expr` constructor of a logical token. -/
def connectiveOf : String → Option String
  | "AND" => some "and" | "OR" => some "or" | _ => none

/-- The {lit}`ArithmeticOperator` constructor of an arithmetic token. -/
def arithmeticOf : String → Option String
  | "PLUS" => some "add" | "MINUS" => some "subtract" | "STAR" => some "multiply" | "SLASH" => some "divide"
  | "REM" => some "remainder" | _ => none

/-- The {lit}`Syntax.RaiseKind` constructor of a {lit}`raisetype` token. -/
def raiseKindOf : String → String
  | "ROLLBACK" => "rollback" | "ABORT" => "abort" | _ => "fail"

/-- A constructor with an operator and two operands: a comparison or an arithmetic operator. -/
def operation (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (kind operator : String)
    (left right : ParseNode) : TranslateM Located := do
  let leftPart ← mappers.expression tree left
  let rightPart ← mappers.expression tree right
  return constructor kind #[("operator", leaf operator node.start node.stop), ("left", leftPart),
    ("right", rightPart)] node.start node.stop

/-- A constructor of one operand. -/
def unary (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (kind : String) (operand : ParseNode) :
    TranslateM Located := do
  return constructor kind #[("operand", ← mappers.expression tree operand)] node.start node.stop

/-- A call of the function with its arguments in written order. -/
def call (mappers : Mappers) (tree : SqlTree) (start stop : Nat) (function : Located)
    (arguments : Array ParseNode) : TranslateM Located := do
  let items ← arguments.mapM (mappers.expression tree)
  let listed := sequence items (items[0]?.map (·.start) |>.getD stop) (items.back?.map (·.stop) |>.getD stop)
  return constructor "call" #[("name", function), ("arguments", listed)] start stop

/-- A call with {lit}`*`, or with zero or more arguments, with the function name as written. -/
def functionCall (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM Located := do
  let function ← if parts[0]!.symbol == "ID" then plainName tree parts[0]!
    else pure (leaf (tree.text parts[0]!) parts[0]!.start parts[0]!.stop)
  match (parts.extract 1 parts.size).toList.map (·.symbol) with
  | ["LP", "STAR", "RP"] => return constructor "callStar" #[("name", function)] node.start node.stop
  | ["LP", "distinct", "exprlist", "RP"] =>
    absent parts[2]! "DISTINCT in a function call"
    call mappers tree node.start node.stop function (← expressionList tree parts[3]!)
  | _ => unsupported node ("A function call with ORDER BY, FILTER or OVER is not modeled; " ++
      "write the call with its arguments only")

/-- {lit}`x LIKE p [ESCAPE e]` and the other {lit}`likeop` operators: a call of the function named
by the operator, with the pattern first, the operand second and the escape last, and
{lit}`not` around it for {lit}`NOT`. -/
def like (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) : TranslateM Located := do
  let operator := tree.children parts[1]!
  let keyword := operator.back!
  let arguments := #[parts[2]!, parts[0]!] ++ (if parts.size == 5 then #[parts[4]!] else #[])
  let called ← call mappers tree node.start node.stop (leaf (tree.text keyword) keyword.start keyword.stop) arguments
  if tree.symbols parts[1]! == ["NOT", "LIKE_KW"] then
    return constructor "not" #[("operand", called)] node.start node.stop
  return called

/-- The binary forms {lit}`expr OP expr`: comparison, {lit}`IS`, connective and arithmetic. -/
def binaryForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) (symbol : String) :
    Option (TranslateM Located) :=
  match comparisonOf symbol, connectiveOf symbol, arithmeticOf symbol with
  | some operator, _, _ => some (operation mappers tree node "compare" operator parts[0]! parts[2]!)
  | none, some kind, _ => some do
    let left ← mappers.expression tree parts[0]!
    let right ← mappers.expression tree parts[2]!
    return constructor kind #[("left", left), ("right", right)] node.start node.stop
  | none, none, some operator => some (operation mappers tree node "arithmetic" operator parts[0]! parts[2]!)
  | none, none, none =>
    if symbol == "IS" then some (operation mappers tree node "compare" "is" parts[0]! parts[2]!) else none

/-- {lit}`RAISE(IGNORE)` and {lit}`RAISE(kind, message)`. -/
def raiseForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) (ignore : Bool) :
    TranslateM Located := do
  if ignore then
    return constructor "raise" #[("kind", leaf "ignore" parts[2]!.start parts[2]!.stop),
      ("message", leaf .null node.start node.stop)] node.start node.stop
  let kind := (tree.children parts[2]!)[0]!
  return constructor "raise" #[("kind", leaf (raiseKindOf kind.symbol) kind.start kind.stop),
    ("message", ← mappers.expression tree parts[4]!)] node.start node.stop

end Belay.Sqlite.Translation
