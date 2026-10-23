import Belay.Sqlite.Translation.Shapes
import Belay.Sqlite.Translation.Parameters

set_option doc.verso true

/-! Names, literals and the expressions outside queries. The port of
{lit}`belay/sqlite/syntax_expressions.py`: quotes are removed and literal bytes decoded, as
SQLite's tokenizer and {lit}`sqlite3Dequote` do; names keep their case, and numbers keep their
token text. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- The character that closes one of SQLite's quote characters. -/
def closingQuote : Char → Option Char
  | '"' => some '"'
  | '\'' => some '\''
  | '`' => some '`'
  | '[' => some ']'
  | _ => none

/-- The characters after an opening quote up to its closing quote, with doubled closing quotes
undoubled. -/
def unquote (close : Char) : List Char → List Char
  | first :: second :: rest =>
    if first == close then (if second == close then close :: unquote close rest else [])
    else first :: unquote close (second :: rest)
  | [first] => if first == close then [] else [first]
  | [] => []

/-- {lit}`sqlite3Dequote`: remove a leading quote up to its closing quote and undouble it. A text
without a leading quote stays as it is; like SQLite, the result ends at the first closing
quote, so {lit}`"Some" Type` becomes {lit}`Some`. -/
def dequote (text : String) : String :=
  match text.toList with
  | first :: rest => match closingQuote first with
    | some close => String.ofList (unquote close rest)
    | none => text
  | [] => text

/-- The single token of a one-token production, or its refusal. -/
def token (tree : SqlTree) (node : ParseNode) : TranslateM ParseNode := do
  let parts := tree.children node
  if parts.size == 1 && parts[0]!.children.isEmpty then return parts[0]!
  unsupported node s!"Unsupported SQL form: {node.symbol}; write a plain name or literal"

/-- An {lit}`nm` production or a name token as written, with its quotes removed. -/
def plainName (tree : SqlTree) (node : ParseNode) : TranslateM (Located String) := do
  let item ← if node.children.isEmpty then pure node else token tree node
  return leaf (dequote (tree.text item)) node.start node.stop

/-- The name of an {lit}`nm` production or a name token as an {name}`Identifier`. -/
def identifierName (tree : SqlTree) (node : ParseNode) : TranslateM (Located Identifier) :=
  (·.map Identifier.ofString) <$> plainName tree node

/-- The value of a hexadecimal digit. -/
def hexDigit (character : Char) : Option Nat :=
  if '0' ≤ character && character ≤ '9' then some (character.toNat - '0'.toNat)
  else if 'a' ≤ character && character ≤ 'f' then some (character.toNat - 'a'.toNat + 10)
  else if 'A' ≤ character && character ≤ 'F' then some (character.toNat - 'A'.toNat + 10)
  else none

/-- The bytes of pairs of hexadecimal digits. -/
def hexBytes : List Char → Option (List UInt8)
  | high :: low :: rest => do return ((← hexDigit high) * 16 + (← hexDigit low)).toUInt8 :: (← hexBytes rest)
  | [] => some []
  | [_] => none

/-- A {lit}`term` production: NULL, a numeric, string or blob literal, or a time keyword. -/
def term (tree : SqlTree) (node : ParseNode) : TranslateM (Located Syntax.Expr) := do
  let item ← token tree node
  let text := tree.text item
  let literal (value : Syntax.Expr) := composite value node.start node.stop #[spanOf item]
  match item.symbol with
  | "NULL" => return leaf .null node.start node.stop
  | "INTEGER" | "FLOAT" | "QNUMBER" => return literal (.numeric text)
  | "STRING" => return literal (.string (dequote text).toUTF8.toList)
  | "BLOB" =>
    match hexBytes ((text.toList.drop 2).dropLast) with
    | some bytes => return literal (.blob bytes)
    | none => unsupported node "A blob literal needs pairs of hexadecimal digits; correct the literal"
  | "CTIME_KW" => return literal (.currentTime text)
  | symbol => unsupported node s!"Unsupported literal: {symbol}; write NULL, a number, a string or a blob"

/-- How an identifier was quoted, from its first character. -/
def quoteKind (text : String) : Syntax.QuoteKind :=
  match text.toList.head? with
  | some '"' => .double
  | some '[' => .bracket
  | some '`' => .backtick
  | _ => .none

/-- An identifier token, with how it was quoted. -/
def identifier (tree : SqlTree) (node : ParseNode) : Located Syntax.Expr :=
  let text := tree.text node
  composite (.identifier (Identifier.ofString (dequote text)) (quoteKind text)) node.start node.stop
    #[spanOf node, spanOf node]

/-- The tokens of SQLite's {lit}`expr ::= ID|INDEXED|JOIN_KW` production: those three and the
keywords of {lit}`%fallback ID` in the pinned {lit}`parse.y` of 3.51.0. The parse tree keeps a
fallback keyword's own symbol, so a column named {lit}`key` is an {lit}`expr` of one {lit}`KEY`
token. -/
def identifierTokens : List String :=
  "ID INDEXED JOIN_KW ABORT ACTION AFTER ANALYZE ASC ATTACH BEFORE BEGIN BY CASCADE CAST COLUMNKW CONFLICT \
  DATABASE DEFERRED DESC DETACH DO EACH END EXCLUSIVE EXPLAIN FAIL FOR IGNORE IMMEDIATE INITIALLY INSTEAD \
  LIKE_KW MATCH NO PLAN QUERY KEY OF OFFSET PRAGMA RAISE RECURSIVE RELEASE REPLACE RESTRICT ROW ROWS ROLLBACK \
  SAVEPOINT TEMP TRIGGER VACUUM VIEW VIRTUAL WITH WITHOUT NULLS FIRST LAST CURRENT FOLLOWING PARTITION \
  PRECEDING RANGE UNBOUNDED EXCLUDE GROUPS OTHERS TIES GENERATED ALWAYS MATERIALIZED REINDEX RENAME IF".splitOn " "

/-- A parameter token with the number that {name}`numberParameters` gave it. -/
def parameter (node : ParseNode) : TranslateM (Located Syntax.Expr) := do
  match (← get).parameters.lookup node.start with
  | some number => return leaf (.parameter number) node.start node.stop
  | none => unsupported node "A parameter outside a statement is not modeled; write a literal"

/-- An {lit}`expr` production outside a query: a literal, a column name, a parameter or a
sign, or its refusal. -/
partial def expression (tree : SqlTree) (node : ParseNode) : TranslateM (Located Syntax.Expr) := do
  let parts := tree.children node
  match tree.symbols node with
  | ["term"] => term tree parts[0]!
  | ["VARIABLE"] => parameter parts[0]!
  | [symbol] =>
    if identifierTokens.contains symbol then return identifier tree parts[0]!
    unsupported node "Unsupported expression; write a literal, a column name or a sign"
  | ["MINUS", "expr"] =>
    let operand ← expression tree parts[1]!
    return composite (.negate operand.value) node.start node.stop #[operand.span]
  | ["PLUS", "expr"] =>
    let operand ← expression tree parts[1]!
    return composite (.positive operand.value) node.start node.stop #[operand.span]
  | _ => unsupported node "Unsupported expression; write a literal, a column name or a sign"

end Belay.Sqlite.Translation
