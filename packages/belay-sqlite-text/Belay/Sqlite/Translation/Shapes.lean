import Belay.Sqlite.Translation.Tree

set_option doc.verso true

/-! Check the shape of parser productions and flatten SQLite's left-recursive lists. The port of
{lit}`belay/sqlite/syntax_shapes.py`. -/

namespace Belay.Sqlite.Translation

/-- The corrective action for a production that has no syntax constructor. -/
def modeledForms : String :=
  "rewrite it with the modeled forms: CREATE TABLE, CREATE [UNIQUE] INDEX, ALTER TABLE ADD COLUMN, ALTER TABLE RENAME, " ++
  "BEGIN, COMMIT, ROLLBACK, INSERT ... VALUES, UPDATE ... SET ... [WHERE column = value] and " ++
  "SELECT ... FROM table [WHERE] [GROUP BY] [ORDER BY] [LIMIT]"

/-- The refusal of a production whose symbols are not the ones that the translation maps. -/
def unsupportedForm (node : ParseNode) : TranslateM α :=
  unsupported node s!"Unsupported SQL form: {node.symbol}; {modeledForms}"

/-- The parts of a production with exactly these symbols, or its refusal. -/
def require (tree : SqlTree) (node : ParseNode) (symbols : List String) : TranslateM (Array ParseNode) :=
  if tree.symbols node == symbols then pure (tree.children node) else unsupportedForm node

/-- Refuse optional syntax that is present. -/
def absent (node : ParseNode) (feature : String) : TranslateM Unit :=
  if node.children.isEmpty then pure () else unsupported node s!"{feature} is not modeled; remove it"

/-- Flatten a left-recursive list in text order; an empty list node ends the list.
{lit}`shapes` gives the symbols of a list node for each number of parts. Each item is the parts
of one list node after the nested list node. -/
def leftList (tree : SqlTree) (node : ParseNode) (shapes : List (Nat × List String)) :
    TranslateM (Array (Array ParseNode)) := do
  let mut items : Array (Array ParseNode) := #[]
  let mut current := node
  let mut fuel := tree.nodes.size + 1
  while !current.children.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let parts := tree.children current
    match shapes.lookup parts.size with
    | some expected =>
      unless tree.symbols current == expected do unsupportedForm current
    | none => unsupportedForm current
    if parts[0]!.symbol != current.symbol then
      items := items.push parts
      break
    items := items.push (parts.extract 1 parts.size)
    current := parts[0]!
  return items.reverse

/-- The last part of a list item. -/
def last (parts : Array ParseNode) : ParseNode := parts.back!

/-- The part at a position from the end of a list item: {lit}`fromEnd parts 1` is the last. -/
def fromEnd (parts : Array ParseNode) (position : Nat) : ParseNode := parts[parts.size - position]!

end Belay.Sqlite.Translation
