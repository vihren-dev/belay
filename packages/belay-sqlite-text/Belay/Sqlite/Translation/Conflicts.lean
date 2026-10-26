import Belay.Sqlite.Translation.Constraints

set_option doc.verso true

/-! The SET lists of UPDATE and DO UPDATE, the ON CONFLICT clauses of INSERT, and the algorithm
of {lit}`INSERT OR algorithm` and {lit}`REPLACE INTO`. The port of
{lit}`belay/sqlite/syntax_conflicts.py`. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- A {lit}`setlist` node as its {lit}`column = expression` pairs in text order. -/
def assignmentList (tree : SqlTree) (assignments : ParseNode) :
    TranslateM (Located (List (Identifier × Syntax.Expr))) := do
  let items ← leftList tree assignments [(3, ["nm", "EQ", "expr"]), (5, ["setlist", "COMMA", "nm", "EQ", "expr"])]
  let pairs ← items.mapM fun item => do
    let column ← identifierName tree (fromEnd item 3)
    let value ← queryExpression tree (last item)
    return pair column value (fromEnd item 3).start (last item).stop
  return sequence pairs assignments.start assignments.stop

/-- One column of a conflict target: a plain name without a direction or {lit}`NULLS`. -/
def targetColumn (tree : SqlTree) (item : Array ParseNode) : TranslateM (Located Identifier) := do
  let expression := fromEnd item 3
  absent (fromEnd item 2) "A direction in an ON CONFLICT target"
  absent (last item) "NULLS FIRST or NULLS LAST in an ON CONFLICT target"
  let located ← queryExpression tree expression
  let refusal := "Only column names are modeled in an ON CONFLICT target; write the column names"
  match located.value with
  | .identifier column _ =>
    -- The name's range is the first part of an identifier (`identifier`); the whole range
    -- stands in if the shape changes.
    return { value := column, span := located.span.parts[0]?.getD located.span }
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .qualified _ _ _ | .negate _ | .positive _
  | .compare _ _ _ | .and _ _ | .or _ _ | .not _ | .isNull _ _ | .callStar _ | .call _ _ | .arithmetic _ _ _
  | .cast _ _ | .collate _ _ | .exists _ | .inQuery _ _ _ | .subquery _ | .inList _ _ _ | .between _ _ _ _
  | .caseOf _ _ | .concatenate _ _ | .raise _ _ => unsupported expression refusal

/-- The target {lit}`(sortlist) where_opt` of a clause as its column names. -/
def conflictTarget (tree : SqlTree) (columns condition : ParseNode) : TranslateM (Located (List Identifier)) := do
  absent condition "A WHERE clause of an ON CONFLICT target"
  let items ← leftList tree columns [(3, ["expr", "sortorder", "nulls"]), (5, ["sortlist", "COMMA", "expr", "sortorder", "nulls"])]
  return sequence (← items.mapM (targetColumn tree)) columns.start columns.stop

/-- {lit}`DO UPDATE SET setlist where_opt` as the {lit}`update` action. -/
def updateAction (tree : SqlTree) (assignments condition : ParseNode) (start stop : Nat) :
    TranslateM (Located Syntax.ConflictAction) := do
  let parts := tree.children condition
  let filter ← if parts.isEmpty then pure (missing condition.start condition.stop)
    else Located.present <$> queryExpression tree parts[1]!
  let pairs ← assignmentList tree assignments
  return composite (.update pairs.value filter.value) start stop #[pairs.span, filter.span]

/-- An absent conflict target, at the position after {lit}`CONFLICT`. -/
def noTarget (conflict : ParseNode) : Located (Option (List Identifier)) := missing conflict.stop conflict.stop

/-- The ON CONFLICT clauses of an {lit}`upsert` node in written order, and the parts
{lit}`RETURNING selcollist`, empty without RETURNING. -/
def conflictClauses (tree : SqlTree) (upsert : ParseNode) :
    TranslateM (Located (List Syntax.ConflictClause) × Array ParseNode) := do
  let mut clauses : Array (Located Syntax.ConflictClause) := #[]
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
        let target ← conflictTarget tree parts[3]! parts[5]!
        pure (target.present, leaf Syntax.ConflictAction.nothing parts[6]!.start parts[7]!.stop)
      | ["ON", "CONFLICT", "LP", "sortlist", "RP", "where_opt", "DO", "UPDATE", "SET", "setlist", "where_opt", "upsert"] => do
        let target ← conflictTarget tree parts[3]! parts[5]!
        pure (target.present, ← updateAction tree parts[9]! parts[10]! parts[6]!.start parts[10]!.stop)
      | ["ON", "CONFLICT", "DO", "NOTHING", "returning"] =>
        pure (noTarget parts[1]!, leaf Syntax.ConflictAction.nothing parts[2]!.start parts[3]!.stop)
      | _ => do
        discard <| require tree current ["ON", "CONFLICT", "DO", "UPDATE", "SET", "setlist", "where_opt", "returning"]
        pure (noTarget parts[1]!, ← updateAction tree parts[5]! parts[6]! parts[2]!.start parts[6]!.stop)
    clauses := clauses.push (composite { target := target.value, action := action.value } parts[0]!.start
      (fromEnd parts 2).stop #[target.span, action.span])
    current := parts.back!
  return (sequence clauses upsert.start upsert.stop, #[])

/-- The algorithm of an {lit}`insert_cmd` node: {lit}`replace` for {lit}`REPLACE INTO`, the
algorithm of {lit}`INSERT OR algorithm`, or none for a plain {lit}`INSERT`. -/
def insertAlgorithm (tree : SqlTree) (operation : ParseNode) : TranslateM (Located (Option ConflictAlgorithm)) := do
  if tree.symbols operation == ["REPLACE"] then return leaf (some .replace) operation.start operation.stop
  let conflict := (← require tree operation ["INSERT", "orconf"])[1]!
  if conflict.children.isEmpty then return missing conflict.start conflict.stop
  return (resolveType tree (← require tree conflict ["OR", "resolvetype"])[1]!).present

end Belay.Sqlite.Translation
