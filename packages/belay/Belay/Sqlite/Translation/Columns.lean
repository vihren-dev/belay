import Belay.Sqlite.Translation.Constraints

set_option doc.verso true

/-! Column definitions and their constraints. The port of {lit}`column_constraint` and
{lit}`column_definition` of {lit}`belay/sqlite/syntax_definitions.py`. -/

namespace Belay.Sqlite.Translation

/-- A {lit}`DEFAULT` constraint's value with its text. -/
def defaultConstraint (tree : SqlTree) (node : ParseNode) (value : Located) : Located :=
  constructor "default" #[("value", value), ("sourceText", leaf (tree.slice value.start value.stop) value.start value.stop)]
    node.start node.stop

/-- A column constraint: NOT NULL, PRIMARY KEY with its sort order, UNIQUE, each with its ON
CONFLICT algorithm, COLLATE, CHECK with the label of the constraint name in effect, REFERENCES,
AS for a generated column, and the DEFAULT forms. -/
def columnConstraint (tree : SqlTree) (node : ParseNode) (current : Option String) : TranslateM Located := do
  let parts := tree.children node
  match tree.symbols node with
  | ["CHECK", "LP", "expr", "RP"] => check tree node parts current
  | ["REFERENCES", "nm", "eidlist_opt", "refargs"] => references tree node parts
  | ["AS", "generated"] => generated tree node parts[1]!
  | ["NOT", "NULL", "onconf"] =>
    return constructor "notNull" #[("algorithm", ← constraintAlgorithm tree parts[2]!)] node.start node.stop
  | ["PRIMARY", "KEY", "sortorder", "onconf", "autoinc"] =>
    absent parts[4]! "AUTOINCREMENT"
    let descending := leaf (tree.symbols parts[2]! == ["DESC"]) parts[2]!.start parts[2]!.stop
    return constructor "primaryKey" #[("descending", descending),
      ("algorithm", ← constraintAlgorithm tree parts[3]!)] node.start node.stop
  | ["UNIQUE", "onconf"] =>
    return constructor "unique" #[("algorithm", ← constraintAlgorithm tree parts[1]!)] node.start node.stop
  | ["COLLATE", "ID"] | ["COLLATE", "STRING"] =>
    return constructor "collate" #[("name", ← plainName tree parts[1]!)] node.start node.stop
  | ["DEFAULT", "scantok", "term"] => return defaultConstraint tree node (← term tree parts[2]!)
  | ["DEFAULT", "MINUS", "scantok", "term"] | ["DEFAULT", "PLUS", "scantok", "term"] =>
    let kind := if parts[1]!.symbol == "MINUS" then "negate" else "positive"
    let value := constructor kind #[("operand", ← term tree parts[3]!)] parts[1]!.start parts[3]!.stop
    return defaultConstraint tree node value
  | ["DEFAULT", "scantok", "ID"] => return defaultConstraint tree node (identifier tree parts[2]!)
  | _ => unsupported node ("Unsupported column constraint; use NOT NULL, PRIMARY KEY, UNIQUE, " ++
      "COLLATE, CHECK, REFERENCES or DEFAULT with a literal")

/-- A column's name, its declared type text as SQLite's tokens leave it, and its constraints,
with the constraint name in effect after them. {lit}`CONSTRAINT name` maps to no constraint, as
it only labels later CHECK constraints. -/
def columnDefinition (tree : SqlTree) (column constraints : ParseNode) : TranslateM (Located × Option String) := do
  let parts ← require tree column ["nm", "typetoken"]
  let typeToken := parts[1]!
  let declared := if typeToken.children.isEmpty then Lean.Json.null
    else .str (dequote (declaredType (tree.text typeToken)))
  let mut items : Array Located := #[]
  let mut current : Option String := none
  for item in ← leftList tree constraints [(2, ["carglist", "ccons"])] do
    let constraint := last item
    let constraintParts := tree.children constraint
    match tree.symbols constraint with
    | ["CONSTRAINT", "nm"] => current := some (constraintName tree constraintParts[1]!)
    | ["defer_subclause"] => items := items.push (deferral tree constraintParts[0]!)
    | _ => items := items.push (← columnConstraint tree constraint current)
  let definition := structure' #[("name", ← plainName tree parts[0]!),
    ("declaredType", leaf declared typeToken.start typeToken.stop),
    ("constraints", sequence items constraints.start constraints.stop)] column.start constraints.stop
  return (definition, current)

end Belay.Sqlite.Translation
