import Belay.Sqlite.Parse
import Belay.Sqlite.ParserLibrary
import Belay.Sqlite.Translation.Schema
import Belay.Sqlite.Translation.Tables
import Belay.Sqlite.Translation.Triggers

set_option doc.verso true

/-! A parsed SQL script as the model's statement syntax with ranges (ADR 0017, S1, prototype 2,
candidate A). The port of {lit}`commands`, {lit}`statement` and {lit}`statements` of
{lit}`belay/sqlite/syntax.py`, and of the refusals of {lit}`sql_tree.py`'s parse. -/

namespace Belay.Sqlite.Translation

/-- The commands of the script in text order; a wrapper such as EXPLAIN is refused. -/
def commands (tree : SqlTree) (root : Nat) : TranslateM (Array ParseNode) := do
  let mut result : Array ParseNode := #[]
  let mut pending : Array ParseNode := #[tree.nodes[root]!]
  let mut fuel := tree.nodes.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    let some node := pending.back? | break
    pending := pending.pop
    pending := pending ++ (tree.children node).reverse
    if node.symbol != "ecmd" then continue
    match tree.symbols node with
    | ["SEMI"] => pure ()
    | ["cmdx", "SEMI"] => result := result.push (tree.children (tree.children node)[0]!)[0]!
    | _ => unsupported node "Unsupported command wrapper, such as EXPLAIN; remove it"
  return result

/-- One command as a statement, or the refusal of a statement that has no syntax constructor. -/
def statement (tree : SqlTree) (command : ParseNode) : TranslateM Located := do
  let symbols := tree.symbols command
  if symbols == ["create_table", "create_table_args"] then return ← createTable tree command
  if symbols.take 3 == ["createkw", "uniqueflag", "INDEX"] then return ← createIndex tree command
  if symbols.take 2 == ["ALTER", "TABLE"] then return ← addColumn tree command
  if symbols == ["createkw", "trigger_decl", "BEGIN", "trigger_cmd_list", "END"] then return ← createTrigger tree command
  if [["DROP", "TABLE"], ["DROP", "INDEX"], ["DROP", "TRIGGER"]].contains (symbols.take 2) then return ← drop tree command
  if [["BEGIN"], ["COMMIT"], ["END"], ["ROLLBACK"]].contains (symbols.take 1) then return ← transaction tree command
  if symbols.take 2 == ["with", "insert_cmd"] then return ← insert tree command
  if symbols.take 2 == ["with", "UPDATE"] then return ← update tree command
  if symbols.take 2 == ["with", "DELETE"] then return ← delete tree command
  if symbols == ["select"] then
    let (clauses, items) ← statementSubqueries (queryClauses tree (tree.children command)[0]!)
    return withSubqueries "select" (clauses.extract 0 8) items command.start command.stop (clauses.extract 8 clauses.size)
  if symbols.take 1 == ["PRAGMA"] then return ← pragma tree command
  unsupported command ("This statement is not modeled; the model runs CREATE TABLE, CREATE INDEX, " ++
    "CREATE TRIGGER, ALTER TABLE ADD COLUMN, DROP TABLE, DROP INDEX, DROP TRIGGER, BEGIN, COMMIT, " ++
    "ROLLBACK, INSERT, UPDATE, DELETE, SELECT and PRAGMA foreign_keys")

/-- Every command of a parsed script as a statement, in order. -/
def statements (tree : SqlTree) (root : Nat) : TranslateM (Array Located) := do
  (← commands tree root).mapM (statement tree)

/-- The translation of a parse result: the statements with their ranges, or the refusal, with
the statuses and messages of the Python frontend for a grammar error and the parser's limits. -/
def translateParse (sql : String) : ParseResult → Except Refusal (Array Located)
  | .parsed nodes root => (statements { sql := sql.toUTF8, nodes } root).run' {}
  | .inputError offset => throw (Refusal.mk "INPUT_ERROR"
      "SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again" offset 0)
  | .resourceLimit offset => throw (Refusal.mk "UNVERIFIED" ("SQL exceeds the parser's limits of 1 MiB of input " ++
      "and 200,000 syntax-tree nodes; split the SQL into smaller files") offset 0)

/-- The translation of SQL text with a grammar of the parser library as JSON, in the form that
{lit}`experiments/surface-s1/texts.py` writes the Python translation's result:
{lit}`{"statements": [...]}` with each located statement, or {lit}`{"refusal": diagnostic}` with
the source name {lit}`measured.sql`. It fails when the library gives an unusable document. -/
def translationJson (grammar sql : String) : IO Lean.Json := do
  let document ← ParserLibrary.parse grammar sql
  let parse ← IO.ofExcept ((decodeParse grammar sql.utf8ByteSize document).mapError IO.userError)
  return match translateParse sql parse with
    | .ok items => Lean.Json.mkObj [("statements", .arr (items.map Located.toJson))]
    | .error refusal => Lean.Json.mkObj [("refusal", refusal.toJson "measured.sql")]

end Belay.Sqlite.Translation
