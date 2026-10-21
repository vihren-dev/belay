import Belay.Sqlite.Translation.Constraints

set_option doc.verso true

/-! DROP TABLE, DROP INDEX, DROP TRIGGER, CREATE INDEX and {lit}`PRAGMA foreign_keys`. The port of
{lit}`belay/sqlite/syntax_drops.py`, {lit}`syntax_indexes.py` and {lit}`syntax_pragmas.py`. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- {lit}`DROP TABLE|INDEX|TRIGGER [IF EXISTS] name`, with the name as written. -/
def drop (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let kind := ((tree.children command)[1]?.map (·.symbol)).getD ""
  let parts ← require tree command ["DROP", kind, "ifexists", "fullname"]
  let full := parts[3]!
  unless tree.symbols full == ["nm"] do unsupported full "A schema name is not modeled; remove it"
  let make : Identifier → Bool → Syntax.Statement := match kind with
    | "TABLE" => .dropTable | "INDEX" => .dropIndex | _ => .dropTrigger
  let existsNode := parts[2]!
  let dropped ← identifierName tree (tree.children full)[0]!
  return composite (make dropped.value (!existsNode.children.isEmpty)) command.start command.stop
    #[dropped.span, spanOf existsNode]

/-- {lit}`CREATE [UNIQUE] INDEX name ON table(terms) [WHERE filter]`. -/
def createIndex (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["createkw", "uniqueflag", "INDEX", "ifnotexists", "nm", "dbnm", "ON", "nm",
    "LP", "sortlist", "RP", "where_opt"]
  absent parts[3]! "IF NOT EXISTS"
  absent parts[5]! "A schema name"
  let whereParts := tree.children parts[11]!
  let filter ← if whereParts.isEmpty then pure (missing parts[11]!.start parts[11]!.stop)
    else Located.present <$> queryExpression tree whereParts[1]!
  let indexName ← identifierName tree parts[4]!
  let table ← identifierName tree parts[7]!
  let terms := sequence (← orderTerms queryMappers tree parts[9]!) parts[9]!.start parts[9]!.stop
  return composite (.createIndex indexName.value (!parts[1]!.children.isEmpty) table.value terms.value filter.value)
    command.start command.stop #[indexName.span, spanOf parts[1]!, table.span, terms.span, filter.span]

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
def pragma (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts := tree.children command
  unless parts.size ≥ 3 && asciiEqual (dequote (tree.text parts[1]!)) "foreign_keys" && parts[2]!.children.isEmpty do
    unsupported command "Only PRAGMA foreign_keys is modeled, without a schema name"
  let value ← match tree.symbols command with
    | ["PRAGMA", "nm", "dbnm"] => pure none
    | ["PRAGMA", "nm", "dbnm", "EQ", "nmnum"] | ["PRAGMA", "nm", "dbnm", "LP", "nmnum", "RP"] =>
      some <$> settingValue tree parts[4]!
    | _ => unsupported command pragmaValues
  return composite (.pragmaForeignKeys value) command.start command.stop #[spanOf command]

end Belay.Sqlite.Translation
