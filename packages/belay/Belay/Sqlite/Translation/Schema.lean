import Belay.Sqlite.Translation.Constraints

set_option doc.verso true

/-! DROP TABLE, DROP INDEX, DROP TRIGGER, CREATE INDEX and {lit}`PRAGMA foreign_keys`. The port of
{lit}`belay/sqlite/syntax_drops.py`, {lit}`syntax_indexes.py` and {lit}`syntax_pragmas.py`. -/

namespace Belay.Sqlite.Translation

/-- {lit}`DROP TABLE|INDEX|TRIGGER [IF EXISTS] name`, with the name as written. -/
def drop (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let kind := ((tree.children command)[1]?.map (·.symbol)).getD ""
  let parts ← require tree command ["DROP", kind, "ifexists", "fullname"]
  let full := parts[3]!
  unless tree.symbols full == ["nm"] do unsupported full "A schema name is not modeled; remove it"
  let constructorName := match kind with | "TABLE" => "dropTable" | "INDEX" => "dropIndex" | _ => "dropTrigger"
  let existsNode := parts[2]!
  return constructor constructorName #[("name", ← plainName tree (tree.children full)[0]!),
    ("ifExists", leaf (!existsNode.children.isEmpty) existsNode.start existsNode.stop)] command.start command.stop

/-- {lit}`CREATE [UNIQUE] INDEX name ON table(terms) [WHERE filter]`. -/
def createIndex (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let parts ← require tree command ["createkw", "uniqueflag", "INDEX", "ifnotexists", "nm", "dbnm", "ON", "nm",
    "LP", "sortlist", "RP", "where_opt"]
  absent parts[3]! "IF NOT EXISTS"
  absent parts[5]! "A schema name"
  let whereParts := tree.children parts[11]!
  let filter ← if whereParts.isEmpty then pure (leaf .null parts[11]!.start parts[11]!.stop)
    else queryExpression tree whereParts[1]!
  let indexName ← plainName tree parts[4]!
  let table ← plainName tree parts[7]!
  let terms ← orderTerms queryMappers tree parts[9]!
  return constructor "createIndex" #[("name", indexName),
    ("unique", leaf (!parts[1]!.children.isEmpty) parts[1]!.start parts[1]!.stop), ("table", table),
    ("terms", sequence terms parts[9]!.start parts[9]!.stop), ("filter", filter)] command.start command.stop

/-- The boolean words of {lit}`sqlite3GetBoolean`, in the order that the Python translation
tries them. -/
def booleanWords : List (String × Bool) :=
  [("on", true), ("yes", true), ("true", true), ("off", false), ("no", false), ("false", false)]

/-- The refusal of a {lit}`PRAGMA foreign_keys` value that the model does not read. -/
def pragmaValues : String :=
  "Only on, off, yes, no, true, false, 0 and 1 are modeled as the value of PRAGMA foreign_keys"

/-- The boolean of an {lit}`nmnum` value, or its refusal. -/
def settingValue (tree : SqlTree) (node : ParseNode) : TranslateM Bool := do
  let parts := tree.children node
  match tree.symbols node with
  | ["plus_num"] =>
    if tree.symbols parts[0]! == ["INTEGER"] then
      match tree.text parts[0]! with
      | "0" => return false
      | "1" => return true
      | _ => pure ()
  | ["ON"] | ["nm"] =>
    let word := if parts[0]!.symbol == "nm" then dequote (tree.text parts[0]!) else "on"
    if let some (_, value) := booleanWords.find? fun (known, _) => asciiEqual word known then return value
  | _ => pure ()
  unsupported node pragmaValues

/-- {lit}`PRAGMA foreign_keys [= value]` and {lit}`PRAGMA foreign_keys(value)`, whose value is
none for the query form. -/
def pragma (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let parts := tree.children command
  unless parts.size ≥ 3 && asciiEqual (dequote (tree.text parts[1]!)) "foreign_keys" && parts[2]!.children.isEmpty do
    unsupported command "Only PRAGMA foreign_keys is modeled, without a schema name"
  let value ← match tree.symbols command with
    | ["PRAGMA", "nm", "dbnm"] => pure Lean.Json.null
    | ["PRAGMA", "nm", "dbnm", "EQ", "nmnum"] | ["PRAGMA", "nm", "dbnm", "LP", "nmnum", "RP"] =>
      Lean.Json.bool <$> settingValue tree parts[4]!
    | _ => unsupported command pragmaValues
  return constructor "pragmaForeignKeys" #[("value", leaf value command.start command.stop)] command.start command.stop

end Belay.Sqlite.Translation
