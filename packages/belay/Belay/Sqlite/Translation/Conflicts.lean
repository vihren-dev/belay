import Belay.Sqlite.Translation.Constraints

set_option doc.verso true

/-! The SET lists of UPDATE and DO UPDATE, the ON CONFLICT clauses of INSERT, and the algorithm
of {lit}`INSERT OR algorithm` and {lit}`REPLACE INTO`. The port of
{lit}`belay/sqlite/syntax_conflicts.py`. -/

namespace Belay.Sqlite.Translation

/-- A {lit}`setlist` node as its {lit}`column = expression` pairs in text order. -/
def assignmentList (tree : SqlTree) (assignments : ParseNode) : TranslateM Located := do
  let items ← leftList tree assignments [(3, ["nm", "EQ", "expr"]), (5, ["setlist", "COMMA", "nm", "EQ", "expr"])]
  let pairs ← items.mapM fun item => do
    let column ← plainName tree (fromEnd item 3)
    let value ← queryExpression tree (last item)
    return pair column value (fromEnd item 3).start (last item).stop
  return sequence pairs assignments.start assignments.stop

/-- One column of a conflict target: a plain name without a direction or {lit}`NULLS`. -/
def targetColumn (tree : SqlTree) (item : Array ParseNode) : TranslateM Located := do
  let expression := fromEnd item 3
  absent (fromEnd item 2) "A direction in an ON CONFLICT target"
  absent (last item) "NULLS FIRST or NULLS LAST in an ON CONFLICT target"
  let located ← queryExpression tree expression
  match located.value.getObjVal? "identifier", located.children[0]? with
  | .ok _, some column => return column
  | _, _ => unsupported expression "Only column names are modeled in an ON CONFLICT target; write the column names"

/-- The target {lit}`(sortlist) where_opt` of a clause as its column names. -/
def conflictTarget (tree : SqlTree) (columns condition : ParseNode) : TranslateM Located := do
  absent condition "A WHERE clause of an ON CONFLICT target"
  let items ← leftList tree columns [(3, ["expr", "sortorder", "nulls"]), (5, ["sortlist", "COMMA", "expr", "sortorder", "nulls"])]
  return sequence (← items.mapM (targetColumn tree)) columns.start columns.stop

/-- {lit}`DO UPDATE SET setlist where_opt` as the {lit}`update` action. -/
def updateAction (tree : SqlTree) (assignments condition : ParseNode) (start stop : Nat) : TranslateM Located := do
  let parts := tree.children condition
  let filter ← if parts.isEmpty then pure (leaf .null condition.start condition.stop) else queryExpression tree parts[1]!
  return constructor "update" #[("assignments", ← assignmentList tree assignments), ("filter", filter)] start stop

/-- The ON CONFLICT clauses of an {lit}`upsert` node in written order, and the parts
{lit}`RETURNING selcollist`, empty without RETURNING. -/
def conflictClauses (tree : SqlTree) (upsert : ParseNode) : TranslateM (Located × Array ParseNode) := do
  let mut clauses : Array Located := #[]
  let mut current := upsert
  let mut fuel := tree.nodes.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    let parts := tree.children current
    let symbols := tree.symbols current
    if symbols == [] || symbols == ["RETURNING", "selcollist"] then
      return (sequence clauses upsert.start upsert.stop, parts)
    let (target, action) ← match symbols with
      | ["ON", "CONFLICT", "LP", "sortlist", "RP", "where_opt", "DO", "NOTHING", "upsert"] => do
        pure (← conflictTarget tree parts[3]! parts[5]!, leaf "nothing" parts[6]!.start parts[7]!.stop)
      | ["ON", "CONFLICT", "LP", "sortlist", "RP", "where_opt", "DO", "UPDATE", "SET", "setlist", "where_opt", "upsert"] => do
        let target ← conflictTarget tree parts[3]! parts[5]!
        pure (target, ← updateAction tree parts[9]! parts[10]! parts[6]!.start parts[10]!.stop)
      | ["ON", "CONFLICT", "DO", "NOTHING", "returning"] =>
        pure (leaf .null parts[1]!.stop parts[1]!.stop, leaf "nothing" parts[2]!.start parts[3]!.stop)
      | _ => do
        discard <| require tree current ["ON", "CONFLICT", "DO", "UPDATE", "SET", "setlist", "where_opt", "returning"]
        pure (leaf .null parts[1]!.stop parts[1]!.stop, ← updateAction tree parts[5]! parts[6]! parts[2]!.start parts[6]!.stop)
    clauses := clauses.push (structure' #[("target", target), ("action", action)] parts[0]!.start (fromEnd parts 2).stop)
    current := parts.back!
  return (sequence clauses upsert.start upsert.stop, #[])

/-- The algorithm of an {lit}`insert_cmd` node: {lit}`replace` for {lit}`REPLACE INTO`, the
algorithm of {lit}`INSERT OR algorithm`, or none for a plain {lit}`INSERT`. -/
def insertAlgorithm (tree : SqlTree) (operation : ParseNode) : TranslateM Located := do
  if tree.symbols operation == ["REPLACE"] then return leaf "replace" operation.start operation.stop
  let conflict := (← require tree operation ["INSERT", "orconf"])[1]!
  if conflict.children.isEmpty then return leaf .null conflict.start conflict.stop
  return resolveType tree (← require tree conflict ["OR", "resolvetype"])[1]!

end Belay.Sqlite.Translation
