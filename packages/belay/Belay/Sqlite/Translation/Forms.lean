import Belay.Sqlite.Translation.Subqueries

set_option doc.verso true

/-! The expression forms of a query that hold subqueries or lists. The port of
{lit}`belay/sqlite/syntax_forms.py`: {lit}`EXISTS (q)`, {lit}`x [NOT] IN (q)` and the scalar
subquery {lit}`(q)` name a subquery of the statement's list; {lit}`x [NOT] IN (values)`,
{lit}`x [NOT] BETWEEN a AND b`, {lit}`CASE ... END` and {lit}`x || y` are their own forms. -/

namespace Belay.Sqlite.Translation

/-- Whether an {lit}`in_op`, {lit}`between_op` node has {lit}`NOT` before its keyword. -/
def negatedOperator (tree : SqlTree) (operator : ParseNode) (keyword : String) : Bool :=
  tree.symbols operator == ["NOT", keyword]

/-- {lit}`EXISTS (q)`, {lit}`x [NOT] IN (q)` and the scalar subquery {lit}`(q)`; none for another
form. -/
def subqueryForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    List String → TranslateM (Option Located)
  | ["LP", "select", "RP"] => do
    let index ← lift mappers tree parts[1]!
    return constructor "subquery" #[("index", leaf index node.start node.stop)] node.start node.stop
  | ["EXISTS", "LP", "select", "RP"] => do
    let index ← lift mappers tree parts[2]!
    return constructor "exists" #[("index", leaf index node.start node.stop)] node.start node.stop
  | ["expr", "in_op", "LP", "select", "RP"] => do
    let operand ← mappers.expression tree parts[0]!
    let negated := negatedOperator tree parts[1]! "IN"
    let index ← lift mappers tree parts[3]!
    return constructor "inQuery" #[("operand", operand), ("index", leaf index node.start node.stop),
      ("negated", leaf negated parts[1]!.start parts[1]!.stop)] node.start node.stop
  | _ => pure none

/-- The expressions of an {lit}`exprlist` node, in text order. -/
def expressionList (tree : SqlTree) (node : ParseNode) : TranslateM (Array ParseNode) := do
  let listed ← leftList tree node [(1, ["nexprlist"])]
  if listed.isEmpty then return #[]
  let items ← leftList tree listed[0]![0]! [(1, ["expr"]), (3, ["nexprlist", "COMMA", "expr"])]
  return items.map last

/-- {lit}`x [NOT] IN (values)`; a list of one parenthesized subquery is {lit}`x IN (SELECT ...)`,
as SQLite's parser reads it. -/
def inList (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM Located := do
  let negated := leaf (negatedOperator tree parts[1]! "IN") parts[1]!.start parts[1]!.stop
  let values ← expressionList tree parts[3]!
  if values.size == 1 && tree.symbols values[0]! == ["LP", "select", "RP"] then
    let index ← lift mappers tree (tree.children values[0]!)[1]!
    return constructor "inQuery" #[("operand", ← mappers.expression tree parts[0]!),
      ("index", leaf index node.start node.stop), ("negated", negated)] node.start node.stop
  let mapped ← values.mapM (mappers.expression tree)
  return constructor "inList" #[("operand", ← mappers.expression tree parts[0]!),
    ("values", sequence mapped parts[3]!.start parts[3]!.stop), ("negated", negated)] node.start node.stop

/-- {lit}`CASE [base] WHEN ... THEN ... [ELSE ...] END`, with its operands in text order. -/
def caseOf (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM Located := do
  let base := tree.children parts[1]!
  let arms ← leftList tree parts[2]! [(4, ["WHEN", "expr", "THEN", "expr"]),
    (5, ["case_exprlist", "WHEN", "expr", "THEN", "expr"])]
  let otherwise := tree.children parts[3]!
  let operands := base ++ arms.flatMap (fun item => #[fromEnd item 3, last item]) ++ otherwise.extract 1 otherwise.size
  let mapped ← operands.mapM (mappers.expression tree)
  return constructor "caseOf" #[("operands", sequence mapped parts[1]!.start parts[3]!.stop),
    ("hasBase", leaf (!base.isEmpty) parts[1]!.start parts[1]!.stop)] node.start node.stop

/-- {lit}`x [NOT] IN (values)`, {lit}`x [NOT] BETWEEN a AND b`, {lit}`CASE ... END` and
{lit}`x || y`; none for another form. -/
def listForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    List String → TranslateM (Option Located)
  | ["expr", "in_op", "LP", "exprlist", "RP"] => some <$> inList mappers tree node parts
  | ["expr", "between_op", "expr", "AND", "expr"] => do
    let negated := negatedOperator tree parts[1]! "BETWEEN"
    let operand ← mappers.expression tree parts[0]!
    let low ← mappers.expression tree parts[2]!
    let high ← mappers.expression tree parts[4]!
    return constructor "between" #[("operand", operand), ("low", low), ("high", high),
      ("negated", leaf negated parts[1]!.start parts[1]!.stop)] node.start node.stop
  | ["CASE", "case_operand", "case_exprlist", "case_else", "END"] => some <$> caseOf mappers tree node parts
  | ["expr", "CONCAT", "expr"] => do
    let left ← mappers.expression tree parts[0]!
    let right ← mappers.expression tree parts[2]!
    return constructor "concatenate" #[("left", left), ("right", right)] node.start node.stop
  | _ => pure none

end Belay.Sqlite.Translation
