import Belay.Sqlite.Translation.Mappers

set_option doc.verso true

/-! CHECK, CONSTRAINT names, foreign keys, generated columns and conflict algorithms of CREATE
TABLE. The port of {lit}`belay/sqlite/syntax_constraints.py` and of {lit}`resolve_type` and
{lit}`constraint_algorithm` of {lit}`syntax_definitions.py`. -/

namespace Belay.Sqlite.Translation

/-- The characters that {lit}`sqlite3Isspace` accepts, which SQLite trims from a CHECK label. -/
def sqliteSpace (character : Char) : Bool := " \t\n\x0c\r\x0b".contains character

/-- The text without the {name}`sqliteSpace` characters at its start and end. -/
def trimSpace (text : String) : String :=
  String.ofList ((text.toList.dropWhile sqliteSpace).reverse.dropWhile sqliteSpace).reverse

/-- The text without the {name}`sqliteSpace` characters at its end. -/
def trimSpaceEnd (text : String) : String := String.ofList (text.toList.reverse.dropWhile sqliteSpace).reverse

/-- Whether the text ends with the lowercase ASCII word, each letter in either ASCII case, as
{lit}`sqlite3_strnicmp` compares a keyword. -/
def endsWithWord (text word : String) : Bool :=
  let characters := text.toList
  let letters := word.toList
  letters.length ≤ characters.length &&
    ((characters.drop (characters.length - letters.length)).zip letters).all fun (character, letter) =>
      character == letter || character.toNat + 32 == letter.toNat

/-- Whether the text is the lowercase ASCII word, each letter in either ASCII case, as
{lit}`sqlite3StrICmp` compares a table option. -/
def asciiEqual (text word : String) : Bool := text.length == word.length && endsWithWord text word

/-- The type text without a trailing {lit}`GENERATED ALWAYS`, as {lit}`sqlite3AddColumn` removes it
before it dequotes the type. -/
def declaredType (text : String) : String :=
  if text.utf8ByteSize ≥ 16 && endsWithWord text "always" then
    let rest := trimSpaceEnd (String.ofList (text.toList.dropLast.dropLast.dropLast.dropLast.dropLast.dropLast))
    if rest.utf8ByteSize ≥ 9 && endsWithWord rest "generated" then
      trimSpaceEnd (String.ofList (rest.toList.take (rest.length - 9)))
    else rest
  else text

/-- The name of a {lit}`CONSTRAINT name` production as SQLite reports it: dequoted. -/
def constraintName (tree : SqlTree) (node : ParseNode) : String := dequote (tree.text node)

/-- The algorithm of a {lit}`resolvetype` node: {lit}`raisetype`, {lit}`IGNORE` or {lit}`REPLACE`. -/
def resolveType (tree : SqlTree) (node : ParseNode) : Located :=
  let part := (tree.children node)[0]!
  let keyword := if part.symbol == "raisetype" then (tree.children part)[0]! else part
  let algorithm := match keyword.symbol with
    | "ROLLBACK" => "rollback" | "ABORT" => "abort" | "FAIL" => "fail" | "IGNORE" => "ignore" | _ => "replace"
  leaf algorithm node.start node.stop

/-- The algorithm of an {lit}`onconf` node, {lit}`ON CONFLICT algorithm`, or none. -/
def constraintAlgorithm (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  if node.children.isEmpty then return leaf .null node.start node.stop
  return resolveType tree (← require tree node ["ON", "CONFLICT", "resolvetype"])[2]!

/-- {lit}`CHECK (expr)` with its label: the name in effect, else the text between the
parentheses, trimmed and dequoted. -/
def check (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) (current : Option String) :
    TranslateM Located := do
  let condition := parts[2]!
  let text := trimSpace (tree.slice parts[1]!.stop parts[3]!.start)
  let label := current.getD (dequote text)
  return constructor "check" #[("condition", ← queryExpression tree condition),
    ("label", leaf label condition.start condition.stop)] node.start node.stop

/-- An {lit}`eidlist` of plain names, without collation or sort order. -/
def plainNames (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  let items ← leftList tree node [(3, ["nm", "collate", "sortorder"]), (5, ["eidlist", "COMMA", "nm", "collate", "sortorder"])]
  let names ← items.mapM fun item => do
    absent (fromEnd item 2) "A collation in a foreign key"
    absent (last item) "A sort order in a foreign key"
    plainName tree (fromEnd item 3)
  return sequence names node.start node.stop

/-- An {lit}`eidlist_opt`: the names of {lit}`(names)`, or no names. -/
def optionalNames (tree : SqlTree) (node : ParseNode) : TranslateM Located := do
  if node.children.isEmpty then return sequence #[] node.start node.stop
  plainNames tree (← require tree node ["LP", "eidlist", "RP"])[1]!

/-- The {lit}`ForeignKeyAction` constructor of a {lit}`refact` production. -/
def foreignKeyAction : List String → String
  | ["SET", "NULL"] => "setNull" | ["SET", "DEFAULT"] => "setDefault" | ["CASCADE"] => "cascade"
  | ["RESTRICT"] => "restrict" | _ => "noAction"

/-- The {lit}`ON DELETE` and {lit}`ON UPDATE` actions of a {lit}`refargs` node, {lit}`noAction`
without a clause; a later clause replaces an earlier one. -/
def actions (tree : SqlTree) (node : ParseNode) : TranslateM (Located × Located) := do
  let mut onDelete := leaf "noAction" node.start node.stop
  let mut onUpdate := leaf "noAction" node.start node.stop
  for item in ← leftList tree node [(2, ["refargs", "refarg"])] do
    let parts := tree.children (last item)
    let symbols := tree.symbols (last item)
    if symbols == ["ON", "DELETE", "refact"] || symbols == ["ON", "UPDATE", "refact"] then
      let action := leaf (foreignKeyAction (tree.symbols parts[2]!)) parts[2]!.start parts[2]!.stop
      if symbols[1]! == "DELETE" then onDelete := action else onUpdate := action
  return (onDelete, onUpdate)

/-- {lit}`AS (expr) [kind]` with the kind token as written, or none. -/
def generated (tree : SqlTree) (node kind : ParseNode) : TranslateM Located := do
  let parts := tree.children kind
  unless (tree.symbols kind).take 3 == ["LP", "expr", "RP"] && parts.size ≤ 4 do
    unsupported kind "Unsupported generated column; write AS (expression) VIRTUAL or STORED"
  let word := if parts.size == 4 then leaf (tree.text parts[3]!) parts[3]!.start parts[3]!.stop
    else leaf .null kind.stop kind.stop
  return constructor "generated" #[("expression", ← queryExpression tree parts[1]!), ("kind", word)] node.start node.stop

/-- A column's {lit}`REFERENCES table [(columns)]` with its actions. -/
def references (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) : TranslateM Located := do
  let (onDelete, onUpdate) ← actions tree parts[3]!
  let table ← plainName tree parts[1]!
  return constructor "references" #[("table", table), ("columns", ← optionalNames tree parts[2]!),
    ("onDelete", onDelete), ("onUpdate", onUpdate)] node.start node.stop

/-- A {lit}`defer_subclause` as {lit}`deferral`, deferred only for
{lit}`DEFERRABLE INITIALLY DEFERRED`, as {lit}`sqlite3DeferForeignKey` receives it. -/
def deferral (tree : SqlTree) (node : ParseNode) : Located :=
  let parts := tree.children node
  let deferred := parts[0]!.symbol == "DEFERRABLE" && tree.symbols parts.back! == ["INITIALLY", "DEFERRED"]
  constructor "deferral" #[("deferred", leaf deferred node.start node.stop)] node.start node.stop

/-- {lit}`FOREIGN KEY (columns) REFERENCES table [(columns)]` with its actions. -/
def foreignKey (tree : SqlTree) (node : ParseNode) (parts : Array ParseNode) : TranslateM Located := do
  let (onDelete, onUpdate) ← actions tree parts[8]!
  let columns ← plainNames tree parts[3]!
  let table ← plainName tree parts[6]!
  return constructor "foreignKey" #[("columns", columns), ("table", table),
    ("referenced", ← optionalNames tree parts[7]!), ("onDelete", onDelete), ("onUpdate", onUpdate)]
    node.start node.stop

end Belay.Sqlite.Translation
