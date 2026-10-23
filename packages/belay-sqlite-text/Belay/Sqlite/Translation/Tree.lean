import Belay.Sqlite.ParseTree
import Belay.Sqlite.Translation.Located

set_option doc.verso true

/-! The parse tree of one SQL text, the refusal of a translation, and the translation's monad
(ADR 0017, S1, prototype 2, candidate A). The port of {lit}`belay/sqlite/sql_tree.py`,
{lit}`errors.py` and the context of {lit}`syntax_subqueries.py`. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model
open Lean (Json)

deriving instance Inhabited for Belay.Sqlite.ParseNode

/-- The range of a node, without parts. -/
def spanOf (node : ParseNode) : Span := { start := node.start, stop := node.stop }

/-- The checked parse tree of an SQL text: the text's UTF-8 bytes and the nodes of the parse
document, which {name}`Belay.Sqlite.decodeParse` checked. -/
structure SqlTree where
  /-- The UTF-8 bytes of the SQL text. -/
  sql : ByteArray
  /-- The nodes; each child index is smaller than its parent's index. -/
  nodes : Array ParseNode

/-- The parts of a node in text order. -/
def SqlTree.children (tree : SqlTree) (node : ParseNode) : Array ParseNode :=
  node.children.map fun index => tree.nodes[index]!

/-- The grammar symbols of a node's parts, which the translation compares with the productions
that it maps. -/
def SqlTree.symbols (tree : SqlTree) (node : ParseNode) : List String :=
  (tree.children node).toList.map (·.symbol)

/-- The text of a byte range; the tokenizer checked that the text is UTF-8, so a range of
whole tokens decodes. -/
def SqlTree.slice (tree : SqlTree) (start stop : Nat) : String :=
  (String.fromUTF8? (tree.sql.extract start stop)).getD ""

/-- The text of a node. -/
def SqlTree.text (tree : SqlTree) (node : ParseNode) : String := tree.slice node.start node.stop

/-- A result that is not a translation: the status, the message for the user and the UTF-8
byte range, as {lit}`belay/sqlite/errors.py` reports it. -/
structure Refusal where
  /-- {lit}`UNSUPPORTED`, {lit}`INPUT_ERROR` or {lit}`UNVERIFIED`. -/
  status : String
  /-- What failed and what the user can do. -/
  message : String
  /-- The first byte of the range. -/
  start : Nat
  /-- The byte after the range, or 0 for a position. -/
  stop : Nat
  deriving Inhabited

/-- The refusal as the diagnostic of the Python frontend, with the source name. -/
def Refusal.toJson (refusal : Refusal) (source : String) : Json :=
  Json.mkObj [("status", refusal.status), ("message", refusal.message), ("source", source),
    ("start", refusal.start), ("end", refusal.stop)]

/-- The subqueries of one statement so far, in the order of their text, and the index of the
subquery being mapped. A slot is empty until its subquery is mapped. -/
structure SubqueryList where
  /-- The mapped subqueries. -/
  items : Array (Option (Located Syntax.Subquery)) := #[]
  /-- The subquery whose clauses are mapped now, or none for the statement's own query. -/
  current : Option Nat := none

/-- The refusal of a subquery outside a statement that lists subqueries. -/
def outsideStatement : String :=
  "A subquery is modeled only in SELECT, INSERT VALUES, UPDATE and DELETE; rewrite the statement without it"

/-- Where the translation is: the open subquery list, if any, and the refusal of a subquery
where none is open. -/
structure Scope where
  /-- The list of the statement whose expressions are mapped. -/
  active : Option SubqueryList := none
  /-- The refusal of a subquery where no list is open. -/
  refusal : String := outsideStatement

/-- The translation's monad: the scope, and a refusal that ends the translation. -/
abbrev TranslateM := StateT Scope (Except Refusal)

/-- Refuse a node: the model has no syntax for it. -/
def unsupported (node : ParseNode) (message : String) : TranslateM α :=
  throw { status := "UNSUPPORTED", message, start := node.start, stop := node.stop }

end Belay.Sqlite.Translation
