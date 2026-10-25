import Belay.Sqlite.Translation.Subqueries
import Belay.Sqlite.Translation.Expressions

set_option doc.verso true

/-! Ordinary WITH definitions enter the same indexed syntax list as other queries.
The model chooses the definitions that each source reference uses. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- The optional output names of a CTE or view, including their source spans.
SQLite reports a syntax error for COLLATE or a sort direction in this list. -/
def queryColumnNames (tree : SqlTree) (node : ParseNode) :
    TranslateM (Located (Option (List Identifier))) := do
  if node.children.isEmpty then return missing node.start node.stop
  let listed := (← require tree node ["LP", "eidlist", "RP"])[1]!
  let items ← leftList tree listed [(3, ["nm", "collate", "sortorder"]),
    (5, ["eidlist", "COMMA", "nm", "collate", "sortorder"])]
  let names ← items.mapM fun item => do
    let name ← identifierName tree (fromEnd item 3)
    unless (fromEnd item 2).children.isEmpty && (last item).children.isEmpty do
      throw {
        status := "INPUT_ERROR", start := name.span.start, stop := (last item).stop
        message := s!"SQLite refuses the column list: syntax error after column name \"{name.value}\"; remove COLLATE and sort directions" }
    pure name
  return (sequence names node.start node.stop).present

/-- Translate one WITH list in written order. Duplicate names are parser errors even
when their definitions are unused. Materialization hints remain model restrictions. -/
def commonTableList (mappers : Mappers) (tree : SqlTree) (node : ParseNode) : TranslateM Unit := do
  let listed ← leftList tree node [(1, ["wqitem"]), (3, ["wqlist", "COMMA", "wqitem"])]
  let mut names : List Identifier := []
  let mut definitions : Array (Located Syntax.CommonTable × ParseNode) := #[]
  for item in listed do
    let parts ← require tree (last item) ["withnm", "eidlist_opt", "wqas", "LP", "select", "RP"]
    let name ← identifierName tree (← require tree parts[0]! ["nm"])[0]!
    if names.any (·.sameName name.value) then
      throw {
        status := "INPUT_ERROR", start := name.span.start, stop := name.span.stop
        message := s!"SQLite refuses the WITH clause: duplicate WITH table name: {name.value}; give each definition a distinct name" }
    names := names ++ [name.value]
    let columns ← queryColumnNames tree parts[1]!
    unless tree.symbols parts[2]! == ["AS"] do
      unsupported parts[2]! "CTE materialization hints are not modeled; remove MATERIALIZED or NOT MATERIALIZED"
    definitions := definitions.push
      (composite { name := name.value, columns := columns.value } name.span.start parts[1]!.stop
        #[name.span, columns.span], parts[4]!)
  for (definition, body) in definitions do
    let _ ← liftWith body ((·, ()) <$> mappers.clauses tree body) (some definition)

/-- Translate the optional WITH prefix of a write. The RECURSIVE keyword remains
outside the supported syntax, including when its definitions happen to be nonrecursive. -/
def withDefinitions (mappers : Mappers) (tree : SqlTree) (node : ParseNode) : TranslateM Unit := do
  if node.children.isEmpty then return
  if (tree.symbols node).contains "RECURSIVE" then
    unsupported node "WITH RECURSIVE is not modeled; use ordinary WITH with nonrecursive definitions"
  commonTableList mappers tree (← require tree node ["WITH", "wqlist"])[1]!

end Belay.Sqlite.Translation
