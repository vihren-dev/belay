import Belay.Sqlite.Translation.Subqueries

set_option doc.verso true

/-! The expression forms of a query that hold subqueries or lists. The port of
{lit}`belay/sqlite/syntax_forms.py`: {lit}`EXISTS (q)`, {lit}`x [NOT] IN (q)` and the scalar
subquery {lit}`(q)` name a subquery of the statement's list; {lit}`x [NOT] IN (values)`,
{lit}`x [NOT] BETWEEN a AND b`, {lit}`CASE ... END` and {lit}`x || y` are their own forms. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- Whether an {lit}`in_op`, {lit}`between_op` node has {lit}`NOT` before its keyword. -/
def negatedOperator (tree : SqlTree) (operator : ParseNode) (keyword : String) : Bool :=
  tree.symbols operator == ["NOT", keyword]

/-- A subquery index as a part, at the range of its expression. -/
def indexAt (node : ParseNode) : Span := spanOf node

/-- {lit}`EXISTS (q)`, {lit}`x [NOT] IN (q)` and the scalar subquery {lit}`(q)`; none for another
form. -/
def subqueryForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    List String → TranslateM (Option (Located Syntax.Expr))
  | ["LP", "select", "RP"] => do
    let index ← lift mappers tree parts[1]!
    return some <| composite (.subquery index) node.start node.stop #[indexAt node]
  | ["EXISTS", "LP", "select", "RP"] => do
    let index ← lift mappers tree parts[2]!
    return some <| composite (.exists index) node.start node.stop #[indexAt node]
  | ["expr", "in_op", "LP", "select", "RP"] => do
    let operand ← mappers.expression tree parts[0]!
    let negated := negatedOperator tree parts[1]! "IN"
    let index ← lift mappers tree parts[3]!
    return some <| composite (.inQuery operand.value index negated) node.start node.stop
      #[operand.span, indexAt node, spanOf parts[1]!]
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
    TranslateM (Located Syntax.Expr) := do
  let negated := negatedOperator tree parts[1]! "IN"
  let values ← expressionList tree parts[3]!
  if values.size == 1 && tree.symbols values[0]! == ["LP", "select", "RP"] then
    let index ← lift mappers tree (tree.children values[0]!)[1]!
    let operand ← mappers.expression tree parts[0]!
    return composite (.inQuery operand.value index negated) node.start node.stop
      #[operand.span, indexAt node, spanOf parts[1]!]
  let mapped := sequence (← values.mapM (mappers.expression tree)) parts[3]!.start parts[3]!.stop
  let operand ← mappers.expression tree parts[0]!
  return composite (.inList operand.value mapped.value negated) node.start node.stop
    #[operand.span, mapped.span, spanOf parts[1]!]

/-- {lit}`CASE [base] WHEN ... THEN ... [ELSE ...] END`, with its operands in text order. -/
def caseOf (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    TranslateM (Located Syntax.Expr) := do
  let base := tree.children parts[1]!
  let arms ← leftList tree parts[2]! [(4, ["WHEN", "expr", "THEN", "expr"]),
    (5, ["case_exprlist", "WHEN", "expr", "THEN", "expr"])]
  let otherwise := tree.children parts[3]!
  let operands := base ++ arms.flatMap (fun item => #[fromEnd item 3, last item]) ++ otherwise.extract 1 otherwise.size
  let mapped := sequence (← operands.mapM (mappers.expression tree)) parts[1]!.start parts[3]!.stop
  return composite (.caseOf mapped.value (!base.isEmpty)) node.start node.stop #[mapped.span, spanOf parts[1]!]

/-- {lit}`x [NOT] IN (values)`, {lit}`x [NOT] BETWEEN a AND b`, {lit}`CASE ... END` and
{lit}`x || y`; none for another form. -/
def listForm (mappers : Mappers) (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) :
    List String → TranslateM (Option (Located Syntax.Expr))
  | ["expr", "in_op", "LP", "exprlist", "RP"] => some <$> inList mappers tree node parts
  | ["expr", "between_op", "expr", "AND", "expr"] => do
    let negated := negatedOperator tree parts[1]! "BETWEEN"
    let operand ← mappers.expression tree parts[0]!
    let low ← mappers.expression tree parts[2]!
    let high ← mappers.expression tree parts[4]!
    return some <| composite (.between operand.value low.value high.value negated) node.start node.stop
      #[operand.span, low.span, high.span, spanOf parts[1]!]
  | ["CASE", "case_operand", "case_exprlist", "case_else", "END"] => some <$> caseOf mappers tree node parts
  | ["expr", "CONCAT", "expr"] => do
    let left ← mappers.expression tree parts[0]!
    let right ← mappers.expression tree parts[2]!
    return some <| composite (.concatenate left.value right.value) node.start node.stop #[left.span, right.span]
  | _ => pure none

end Belay.Sqlite.Translation
