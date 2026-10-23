import Lean.Data.Json

set_option doc.verso true

/-! The parser library's parse document, read into a syntax tree. The checks are those of the
Python binding ({lit}`belay/sqlite/sql_tree.py`): every node's range is inside the text, every
child comes before its parent, and the root is the grammar's {lit}`input` production. -/

namespace Belay.Sqlite

open Lean (Json)

/-- One production or token of the parse tree: the grammar symbol, its half-open UTF-8 byte
range in the text, and the indexes of its children in text order. -/
structure ParseNode where
  /-- The grammar symbol, for example {lit}`cmd` or {lit}`SEMI`. -/
  symbol : String
  /-- The first byte of the range. -/
  start : Nat
  /-- The byte after the range. -/
  stop : Nat
  /-- The indexes of the children; each is smaller than the node's own index. -/
  children : Array Nat
  deriving Repr, BEq

/-- The result of a parse: the tree's nodes and the index of its root, or the byte offset
where SQLite's grammar rejects the text, or where the parser stops at its limits of 1 MiB of
input and 200,000 nodes. -/
inductive ParseResult where
  /-- The text parses; {lit}`root` is the index of the {lit}`input` node. -/
  | parsed (nodes : Array ParseNode) (root : Nat)
  /-- SQLite's grammar rejects the text at the byte offset. -/
  | inputError (offset : Nat)
  /-- The text exceeds the parser's limits; the parser stopped at the byte offset. -/
  | resourceLimit (offset : Nat)
  deriving Repr, BEq

/-- A natural number field of a JSON object. -/
def natField (object : Json) (field : String) : Except String Nat := do
  (← object.getObjVal? field).getNat?

/-- One node of the document, checked against the text's length and its own index. -/
def decodeNode (length index : Nat) (item : Json) : Except String ParseNode := do
  let symbol ← (← item.getObjVal? "symbol").getStr?
  let start ← natField item "start"
  let stop ← natField item "end"
  let children ← (← (← item.getObjVal? "children").getArr?).mapM fun child => do
    let position ← child.getNat?
    if position < index then pure position else throw "a child does not come before its parent"
  if start ≤ stop && stop ≤ length then pure { symbol, start, stop, children }
  else throw "a node's range is outside the text"

/-- The parse document of a text of {lit}`length` bytes with the grammar {lit}`grammar`, read and
checked; an error says what is wrong with the document. -/
def decodeParse (grammar : String) (length : Nat) (document : String) : Except String ParseResult := do
  let json ← Json.parse document
  match ← (← json.getObjVal? "status").getStr? with
  | "RESOURCE_LIMIT" => return .resourceLimit ((natField json "offset").toOption.getD 0)
  | "PARSED" =>
    unless (← (← json.getObjVal? "grammar").getStr?) == grammar do throw "the result is for another grammar"
    let items ← (← json.getObjVal? "nodes").getArr?
    let nodes ← (items.zipIdx).mapM fun (item, index) => decodeNode length index item
    let root ← natField json "root"
    match nodes[root]? with
    | some node => if node.symbol == "input" then return .parsed nodes root else throw "the root is not an input node"
    | none => throw "the root is not a node"
  | "INPUT_ERROR" => return .inputError ((natField json "offset").toOption.getD 0)
  | status => throw s!"the status {status} is not one of the library's"

end Belay.Sqlite
