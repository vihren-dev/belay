import Belay.Sqlite.Translation.Sources

set_option doc.verso true

/-! The clauses of a SELECT. The port of {lit}`belay/sqlite/syntax_select.py`: result columns,
the first table and the joins, or none without FROM, and WHERE, GROUP BY, ORDER BY, LIMIT,
OFFSET, HAVING and DISTINCT. Compound SELECT, WITH and NULLS FIRST or LAST are refused. -/

namespace Belay.Sqlite.Translation

/-- The ORDER BY terms of a {lit}`sortlist` in text order, with their direction. -/
def orderTerms (mappers : Mappers) (tree : SqlTree) (node : ParseNode) : TranslateM (Array Located) := do
  let items ← leftList tree node [(3, ["expr", "sortorder", "nulls"]),
    (5, ["sortlist", "COMMA", "expr", "sortorder", "nulls"])]
  items.mapM fun item => do
    let term := fromEnd item 3
    let direction := fromEnd item 2
    absent (last item) "NULLS FIRST or NULLS LAST"
    let descending := tree.symbols direction == ["DESC"]
    let expression ← mappers.expression tree term
    return structure' #[("expression", expression), ("descending", leaf descending direction.start direction.stop)]
      term.start (max term.stop direction.stop)

/-- An optional part: the located value, or a null leaf at the clause. -/
def optionalAt (located : Option Located) (node : ParseNode) : Located :=
  located.getD (leaf .null node.start node.stop)

/-- The LIMIT and OFFSET expressions of a {lit}`limit_opt` node. -/
def limitClause (mappers : Mappers) (tree : SqlTree) (limit : ParseNode) : TranslateM (Option Located × Option Located) := do
  let bounds := tree.children limit
  match tree.symbols limit with
  | [] => return (none, none)
  | ["LIMIT", "expr"] => return (some (← mappers.expression tree bounds[1]!), none)
  | ["LIMIT", "expr", "OFFSET", "expr"] =>
    let first ← mappers.expression tree bounds[1]!
    return (some first, some (← mappers.expression tree bounds[3]!))
  | ["LIMIT", "expr", "COMMA", "expr"] =>
    let first ← mappers.expression tree bounds[1]!
    return (some (← mappers.expression tree bounds[3]!), some first)
  | _ => unsupported limit "Unsupported LIMIT form; write LIMIT n [OFFSET m]"

/-- The clauses of a {lit}`select` production, in the order of {lit}`Syntax.Subquery` and of their
text, so the subqueries of their expressions are listed in that order. -/
def queryClausesWith (mappers : Mappers) (tree : SqlTree) (selectNode : ParseNode) :
    TranslateM (Array (String × Located)) := do
  let current := (← require tree selectNode ["selectnowith"])[0]!
  let one := (← require tree current ["oneselect"])[0]!
  let parts ← require tree one ["SELECT", "distinct", "selcollist", "from", "where_opt", "groupby_opt",
    "having_opt", "orderby_opt", "limit_opt"]
  let (distinct, source, whereNode, group, having, order, limit) :=
    (parts[1]!, parts[3]!, parts[4]!, parts[5]!, parts[6]!, parts[7]!, parts[8]!)
  let results ← resultColumns mappers tree parts[2]!
  let (firstTable, joins) ← if source.children.isEmpty then
      pure (leaf .null source.start source.stop, sequence #[] source.start source.stop)
    else fromClause mappers tree (← require tree source ["FROM", "seltablist"])[1]!
  let condition ← if whereNode.children.isEmpty then pure none
    else some <$> mappers.expression tree (tree.children whereNode)[1]!
  let grouping ← if group.children.isEmpty then pure #[] else do
    let items ← leftList tree (tree.children group)[2]! [(1, ["expr"]), (3, ["nexprlist", "COMMA", "expr"])]
    items.mapM fun item => mappers.expression tree (last item)
  let ordering ← if order.children.isEmpty then pure #[] else orderTerms mappers tree (tree.children order)[2]!
  let (count, offset) ← limitClause mappers tree limit
  let havingPart ← if having.children.isEmpty then pure none
    else some <$> mappers.expression tree (tree.children having)[1]!
  return #[("columns", results), ("source", firstTable), ("joins", joins), ("filter", optionalAt condition whereNode),
    ("groupBy", sequence grouping group.start group.stop), ("orderBy", sequence ordering order.start order.stop),
    ("limit", optionalAt count limit), ("offset", optionalAt offset limit), ("having", optionalAt havingPart having),
    ("distinct", leaf (tree.symbols distinct == ["DISTINCT"]) distinct.start distinct.stop)]

end Belay.Sqlite.Translation
