import Belay.Sqlite.Translation.Constraints

set_option doc.verso true

/-! Column definitions and their constraints. The port of {lit}`column_constraint` and
{lit}`column_definition` of {lit}`belay/sqlite/syntax_definitions.py`. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- A {lit}`DEFAULT` constraint's value with its text. -/
def defaultConstraint (tree : SqlTree) (node : ParseNode) (value : Located Syntax.Expr) : Located Syntax.ColumnConstraint :=
  let text := { value.span with parts := #[] }
  composite (.default value.value (tree.slice text.start text.stop)) node.start node.stop #[value.span, text]

/-- A column constraint: NOT NULL, PRIMARY KEY with its sort order, UNIQUE, each with its ON
CONFLICT algorithm, COLLATE, CHECK with the label of the constraint name in effect, REFERENCES,
AS for a generated column, and the DEFAULT forms. -/
def columnConstraint (tree : SqlTree) (node : ParseNode) (current : Option String) :
    TranslateM (Located Syntax.ColumnConstraint) := do
  let parts := tree.children node
  match tree.symbols node with
  | ["CHECK", "LP", "expr", "RP"] => check tree node parts current .check
  | ["REFERENCES", "nm", "eidlist_opt", "refargs"] => references tree node parts
  | ["AS", "generated"] => generated tree node parts[1]!
  | ["NOT", "NULL", "onconf"] =>
    let algorithm ← constraintAlgorithm tree parts[2]!
    return composite (.notNull algorithm.value) node.start node.stop #[algorithm.span]
  | ["PRIMARY", "KEY", "sortorder", "onconf", "autoinc"] =>
    absent parts[4]! "AUTOINCREMENT"
    let algorithm ← constraintAlgorithm tree parts[3]!
    return composite (.primaryKey (tree.symbols parts[2]! == ["DESC"]) algorithm.value) node.start node.stop
      #[spanOf parts[2]!, algorithm.span]
  | ["UNIQUE", "onconf"] =>
    let algorithm ← constraintAlgorithm tree parts[1]!
    return composite (.unique algorithm.value) node.start node.stop #[algorithm.span]
  | ["COLLATE", "ID"] | ["COLLATE", "STRING"] =>
    let collation ← identifierName tree parts[1]!
    return composite (.collate collation.value) node.start node.stop #[collation.span]
  | ["DEFAULT", "scantok", "term"] => return defaultConstraint tree node (← term tree parts[2]!)
  | ["DEFAULT", "MINUS", "scantok", "term"] | ["DEFAULT", "PLUS", "scantok", "term"] =>
    let operand ← term tree parts[3]!
    let value := if parts[1]!.symbol == "MINUS" then Syntax.Expr.negate operand.value else .positive operand.value
    return defaultConstraint tree node (composite value parts[1]!.start parts[3]!.stop #[operand.span])
  | ["DEFAULT", "scantok", "ID"] => return defaultConstraint tree node (identifier tree parts[2]!)
  | _ => unsupported node ("Unsupported column constraint; use NOT NULL, PRIMARY KEY, UNIQUE, " ++
      "COLLATE, CHECK, REFERENCES or DEFAULT with a literal")

/-- A column's name, its declared type text as SQLite's tokens leave it, and its constraints,
with the constraint name in effect after them. {lit}`CONSTRAINT name` maps to no constraint, as
it only labels later CHECK constraints. -/
def columnDefinition (tree : SqlTree) (column constraints : ParseNode) :
    TranslateM (Located Syntax.ColumnDefinition × Option String) := do
  let parts ← require tree column ["nm", "typetoken"]
  let typeToken := parts[1]!
  let declared := if typeToken.children.isEmpty then none else some (dequote (declaredType (tree.text typeToken)))
  let mut items : Array (Located Syntax.ColumnConstraint) := #[]
  let mut current : Option String := none
  for item in ← leftList tree constraints [(2, ["carglist", "ccons"])] do
    let constraint := last item
    let constraintParts := tree.children constraint
    match tree.symbols constraint with
    | ["CONSTRAINT", "nm"] => current := some (constraintName tree constraintParts[1]!)
    | ["defer_subclause"] => items := items.push (deferral tree constraintParts[0]! .deferral)
    | _ => items := items.push (← columnConstraint tree constraint current)
  let columnName ← identifierName tree parts[0]!
  let listed := sequence items constraints.start constraints.stop
  let definition := composite { name := columnName.value, declaredType := declared, constraints := listed.value }
    column.start constraints.stop #[columnName.span, spanOf typeToken, listed.span]
  return (definition, current)

end Belay.Sqlite.Translation
