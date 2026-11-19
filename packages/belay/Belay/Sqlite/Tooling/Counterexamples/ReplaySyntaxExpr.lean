import Belay.Sqlite.Tooling.Counterexamples.ReplayValues

set_option doc.verso true

/-! Render stored syntax expressions for view and trigger SQL.
Replay validates the reconstructed database before it reports a counterexample. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- A parenthesized SQL expression with two operands. Parentheses preserve the syntax tree when
operators have different precedence. -/
def binarySql (op left right : String) : String := "(" ++ left ++ " " ++ op ++ " " ++ right ++ ")"

/-- The SQL token for a comparison in a catalog expression. For example, equality prints as {lit}`=`. -/
def comparisonSql : Comparison → String
  | .eq => "="
  | .ne => "<>"
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .is => "IS"
  | .isNot => "IS NOT"

/-- The SQL token for the arithmetic operation in a stored expression. -/
def arithmeticSql : ArithmeticOperator → String
  | .add => "+"
  | .subtract => "-"
  | .multiply => "*"
  | .divide => "/"
  | .remainder => "%"

/-- The identifier with its original quote kind. Views retain this distinction because SQLite
resolves a double-quoted identifier differently from an unquoted one. -/
private def quotedName (name : Identifier) (kind : Syntax.QuoteKind) : Option String := do
  let quoted ← identifier name
  match kind with
  | .double => return quoted
  | .none => return name.text
  | .backtick => return "`" ++ name.text.replace "`" "``" ++ "`"
  | .bracket => guard (!name.text.contains ']'); return "[" ++ name.text ++ "]"
  | .single => textLiteral name.bytes

/-- Print the pairs of WHEN and THEN expressions followed by the optional ELSE expression. -/
private def caseArms : List String → String
  | [] => ""
  | [last] => " ELSE " ++ last
  | condition :: result :: rest => " WHEN " ++ condition ++ " THEN " ++ result ++ caseArms rest

/-- Print a stored syntax expression, using the caller's SQL for each subquery position.
For example, a view supplies its list of subqueries, and a trigger with no subqueries
supplies a lookup that always fails. Unrepresentable literals give no SQL. -/
partial def syntaxExprSql (query : Nat → Option String) : Syntax.Expr → Option String
  | .null => some "NULL"
  | .numeric text | .currentTime text => some text
  | .string bytes => textLiteral bytes
  | .blob bytes => some (blobLiteral bytes)
  | .parameter n => some ("?" ++ toString n)
  | .identifier name quote => quotedName name quote
  | .qualified source column schema => do
    let qualifier ← schema.mapM identifier
    return (qualifier.map (· ++ ".")).getD "" ++ (← identifier source) ++ "." ++ (← identifier column)
  | .negate e => return "(-" ++ (← syntaxExprSql query e) ++ ")"
  | .positive e => return "(+" ++ (← syntaxExprSql query e) ++ ")"
  | .not e => return "(NOT " ++ (← syntaxExprSql query e) ++ ")"
  | .isNull e negated => return "(" ++ (← syntaxExprSql query e) ++ (if negated then " IS NOT NULL)" else " IS NULL)")
  | .compare op a b => return binarySql (comparisonSql op) (← syntaxExprSql query a) (← syntaxExprSql query b)
  | .arithmetic op a b => return binarySql (arithmeticSql op) (← syntaxExprSql query a) (← syntaxExprSql query b)
  | .and a b => return binarySql "AND" (← syntaxExprSql query a) (← syntaxExprSql query b)
  | .or a b => return binarySql "OR" (← syntaxExprSql query a) (← syntaxExprSql query b)
  | .concatenate a b => return binarySql "||" (← syntaxExprSql query a) (← syntaxExprSql query b)
  | .callStar name => return (← identifier (Identifier.ofString name)) ++ "(*)"
  | .call name args => do
    let arguments ← args.mapM (syntaxExprSql query)
    if (name == "->" || name == "->>") then
      let [a, b] := arguments | none
      return binarySql name a b
    return (← identifier (Identifier.ofString name)) ++ "(" ++ String.intercalate ", " arguments ++ ")"
  | .cast e typeName => return "CAST(" ++ (← syntaxExprSql query e) ++ " AS " ++ typeName ++ ")"
  | .collate e name => return "(" ++ (← syntaxExprSql query e) ++ " COLLATE " ++ (← identifier name) ++ ")"
  | .exists n => return "EXISTS (" ++ (← query n) ++ ")"
  | .subquery n => return "(" ++ (← query n) ++ ")"
  | .inQuery e n negated => do
    return binarySql (if negated then "NOT IN" else "IN") (← syntaxExprSql query e) ("(" ++ (← query n) ++ ")")
  | .inList e args negated => do
    let items ← args.mapM (syntaxExprSql query)
    return binarySql (if negated then "NOT IN" else "IN") (← syntaxExprSql query e) ("(" ++ String.intercalate ", " items ++ ")")
  | .between e lo hi negated => do
    return "(" ++ (← syntaxExprSql query e) ++ (if negated then " NOT BETWEEN " else " BETWEEN ") ++
      (← syntaxExprSql query lo) ++ " AND " ++ (← syntaxExprSql query hi) ++ ")"
  | .caseOf args base => do
    let parts ← args.mapM (syntaxExprSql query)
    if base then
      let first :: rest := parts | none
      return "CASE " ++ first ++ caseArms rest ++ " END"
    return "CASE" ++ caseArms parts ++ " END"
  | .raise kind message => do
    let action := match kind with
      | .ignore => "IGNORE" | .rollback => "ROLLBACK" | .abort => "ABORT" | .fail => "FAIL"
    let value ← message.mapM (syntaxExprSql query)
    return "RAISE(" ++ action ++ (value.map (", " ++ ·)).getD "" ++ ")"

end Belay.Sqlite.Replay
