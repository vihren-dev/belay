import SelectOneWhereSupport
import SelectGroupSupport

set_option doc.verso true

/-! Support of the claims about
{lit}`SELECT 1 WHERE NOT EXISTS (SELECT c FROM t WHERE w GROUP BY k HAVING count(*) > 1)` over every
database, through the phase rules of ADR 0027: the subquery run rule
({lit}`Resolved.Query.subqueryRun_of_faultless`), the unordered result rule
({lit}`Resolved.Query.results_unordered`), the aggregate records rule ({lit}`Resolved.records_aggregate`),
the grouped rule ({lit}`Resolved.queryGroups_grouped`), the pairwise group rule
({lit}`Resolved.groups_short_iff_pairwise`) and the claims of {lit}`SELECT 1 WHERE c`
({lit}`whereOne_claims`). The fixtures {lit}`ClaimsDuplicateKeys`, {lit}`SuccessUniqueEmail` and
{lit}`GlobalSignupInvariant` use it. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The rows of the table at a position for which the condition {lit}`w`, if any, is true with the
values, in scan order. -/
abbrev keptTableRows (db : Database) (parameters : List Value) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) : List (List Value) :=
  Resolved.keptRows (Resolved.EvalContext.bound parameters) condition
    (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] })

/-- Whether each group of {name}`keptTableRows` by the key {lit}`k` under the collation has at most one
row. -/
abbrev keyGroupsShort (db : Database) (parameters : List Value) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) (key : Resolved.Expr) (collation : Collation) : Bool :=
  (Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
    (keptTableRows db parameters position table condition)).all fun group => decide (group.length ≤ 1)

/-- For every position, calm condition {lit}`c`, calm condition {lit}`w` of the subquery, calm result
column {lit}`e`, name, calm key {lit}`k` and collation, the statement {lit}`SELECT 1 WHERE c` with the
one subquery {lit}`SELECT e FROM t WHERE w GROUP BY k HAVING count(*) > 1` of the first source of a
table is calm ({name}`Resolved.Statement.Calm`). Proof sketch: the expressions of the statement are
{lit}`c`, the literal one, {lit}`w`, {lit}`e`, {lit}`k` and {lit}`count(*) > 1`, which compares an
aggregate value with a literal. -/
theorem duplicateKeys_calm (position : Nat) (main : Resolved.Expr) (condition : Option Resolved.Expr)
    (column : Resolved.Expr) (name : String) (key : Resolved.Expr) (collation : Collation) (mainCalm : main.Calm)
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm) (columnCalm : column.Calm)
    (keyCalm : key.Calm) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.duplicateKeys [.first position] condition column name key collation]).Calm := by
  have expressions : (Resolved.Query.duplicateKeys [.first position] condition column name key collation).expressions =
      condition.toList ++ [column, key, .compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary] := by
    simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.duplicateKeys,
      Resolved.QuerySource.first, Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands]
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions, expressions,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with (rfl | rfl) | member | rfl | rfl | rfl
  · exact mainCalm
  · exact Resolved.Expr.calm_literal _
  · exact conditionCalm expression member
  · exact columnCalm
  · exact keyCalm
  · simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
      Resolved.Expr.readsCounterHere]

/-- For every database with a table at a position under some name, values, calm condition {lit}`w`,
calm result column {lit}`e`, name, calm key {lit}`k` and collation: the run of
{lit}`SELECT e FROM t WHERE w GROUP BY k HAVING count(*) > 1` as a subquery with the values for the
row with no cells has no fault, and has no rows exactly when {name}`keyGroupsShort` is true. Proof
sketch: {name}`Resolved.Query.subqueryRun_of_faultless` with the scan of the table, then
{name}`Resolved.Query.results_unordered`, {name}`Resolved.records_aggregate` and
{name}`Resolved.queryGroups_grouped`; {lit}`HAVING` keeps a group exactly when it has more than one
row ({name}`SelectGroupCases.countCondition_truthy`). -/
theorem duplicateKeysOne_run (db : Database) (parameters : List Value) (name : Identifier) (position : Nat)
    (table : CatalogTable) (condition : Option Resolved.Expr) (column : Resolved.Expr) (columnName : String)
    (key : Resolved.Expr) (collation : Collation) (found : db.raw.catalog.findTable name = some (position, table))
    (calm : ∀ expression ∈ condition.toList, expression.Calm) (columnCalm : column.Calm) (keyCalm : key.Calm) :
    ((Resolved.Query.duplicateKeys [.first position] condition column columnName key collation).subqueryRun
        (Resolved.EvalContext.bound parameters) db.raw []).fault = .none ∧
      ((Resolved.Query.duplicateKeys [.first position] condition column columnName key collation).subqueryRun
        (Resolved.EvalContext.bound parameters) db.raw []).rows.isEmpty =
        keyGroupsShort db parameters position table condition key collation := by
  have plain := (duplicateKeys_calm position _ condition column columnName key collation
    (Resolved.Expr.calm_exists 0) calm columnCalm keyCalm).subquery_plain (List.mem_singleton_self _)
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound parameters) db.raw [] none
    rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none _ position _ [] rfl
      (Database.table_of_findTable db.raw _ position table found)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet parameters)
      row expression (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, Resolved.Query.duplicateKeys, Resolved.Aggregate.fails])
    (by simp [Resolved.Query.distinctCertain, Resolved.Query.duplicateKeys])
  have keeps : ∀ group, (Resolved.Query.duplicateKeys [.first position] condition column columnName key
      collation).keepsGroup (Resolved.EvalContext.bound parameters) group = decide (1 < group.length) := by
    intro group
    show Option.all _ (some (Resolved.Expr.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary)) = _
    rw [Option.all_some, SelectGroupCases.countCondition_truthy _ _ group.length 1 rfl]
    simp only [decide_eq_decide]
    omega
  rw [run]
  refine ⟨rfl, ?_⟩
  rw [Resolved.Query.results_unordered _ rfl rfl rfl rfl rfl, Resolved.records_aggregate _ rfl,
    Resolved.queryGroups_grouped _ (by simp [Resolved.Query.duplicateKeys]), List.filter_congr fun group _ => keeps group]
  apply Bool.eq_iff_iff.mpr
  simp [keyGroupsShort, keptTableRows, Resolved.keptRows, Resolved.filtered, Resolved.outerCells,
    Resolved.Query.duplicateKeys, List.filter_eq_nil_iff]

/-- For every script of one statement
{lit}`SELECT 1 WHERE NOT EXISTS (SELECT e FROM t WHERE w GROUP BY k HAVING count(*) > 1)` with values,
and database with the table {lit}`t` at a position, where {lit}`e`, {lit}`w` and {lit}`k` resolve in the
scope of the table as for {name}`resolveStatement_selectOne_notExists_duplicateKeys` to a calm condition,
a calm result column and a calm key under a collation:

* {name}`Holds` holds exactly when {name}`keyGroupsShort` is true,
* {name (full := Belay.Sqlite.Empty)}`Empty` holds exactly when it is false, and
* {name}`Fails` does not hold.

The table reference names no schema and has no indexed query and no arguments. Proof sketch:
{name}`whereOne_claims` with the resolution; {name}`duplicateKeysOne_run` gives the value of
{lit}`NOT EXISTS`. -/
theorem noDuplicateKeys_claims {script : Script} {isQuery : script.isQuery = true} {db : Database}
    {reference : Syntax.TableReference} {value : Syntax.Expr} {text : String} {filter : Option Syntax.Expr}
    {term : Syntax.Expr} {parameters : List Value} {position : Nat} {table : CatalogTable} {column : Resolved.Expr}
    {columnName : String} {affinity : Option Affinity} {key : Resolved.Expr} {collation : Collation}
    {whereCondition : Option Resolved.Expr} {name : String}
    (head : script.statements = [(.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] []
      none none [Syntax.Subquery.mk [.expression value none text] (some reference) [] filter [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none, parameters)])
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (notCall : aggregateCall value = false) (noCalls : value.aggregateCalls = [])
    (columnResolves : resolveAll (resolveResultColumn runContext.profile.dqsDml
      (tableScope db.raw.catalog reference position table) { current := some 0, aggregates := [.callStar name] })
      [.expression value none text] = .ok [[(.scalar column, columnName, affinity)]])
    (columnGrouped : column.grouped [key] = true)
    (columnFeeds : (column.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false)
    (filterResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      filter whereCondition { current := some 0, aggregates := [.callStar name] })
    (groupResolves : GroupTermResolvesIn runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0, aggregates := [.callStar name] } (.scalar column, columnName, affinity)
      (value.collationIn (tableScope db.raw.catalog reference position table)) term key collation)
    (whereCalm : ∀ expression ∈ whereCondition.toList, expression.Calm) (columnCalm : column.Calm)
    (keyCalm : key.Calm) :
    (Holds script db isQuery ↔ keyGroupsShort db parameters position table whereCondition key collation = true) ∧
      (Belay.Sqlite.Empty script db isQuery ↔
        keyGroupsShort db parameters position table whereCondition key collation = false) ∧
      ¬ Fails script db isQuery := by
  have run := duplicateKeysOne_run db parameters reference.table position table whereCondition column columnName key
    collation found whereCalm columnCalm keyCalm
  obtain ⟨holds, empty, notFails⟩ := whereOne_claims (isQuery := isQuery) _ parameters head db (.not (.exists 0)) _
    (resolveStatement_selectOne_notExists_duplicateKeys runContext (db.raw.connection Env.default.counters).resolveState
      reference value text filter term name count position table column columnName affinity key collation
      whereCondition namedSource current arguments found notCall noCalls columnResolves columnGrouped columnFeeds
      filterResolves groupResolves)
    (duplicateKeys_calm position _ whereCondition column columnName key collation
      ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists 0)) whereCalm columnCalm keyCalm)
    (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]; exact run.1)
  rw [holds, empty, Resolved.Expr.eval_not, Resolved.truthy_not, Resolved.Expr.eval_exists,
    Resolved.EvalContext.statement_one, run.2]
  refine ⟨?_, ?_, notFails⟩ <;>
    cases keyGroupsShort db parameters position table whereCondition key collation <;> simp [Resolved.falsy]

/-- For every values, database, position, table, condition {lit}`w`, key {lit}`k` and collation,
{name}`keyGroupsShort` is true exactly when no row of {name}`keptTableRows` has a key that compares as
equal, under the collation, to the key of a row before it. Two NULL keys compare as equal. Proof
sketch: {name}`Resolved.groups_short_iff_pairwise` with {name}`Resolved.sameGroup_single`. -/
theorem keyGroupsShort_iff_pairwise (db : Database) (parameters : List Value) (position : Nat)
    (table : CatalogTable) (condition : Option Resolved.Expr) (key : Resolved.Expr) (collation : Collation) :
    keyGroupsShort db parameters position table condition key collation = true ↔
      (keptTableRows db parameters position table condition).Pairwise fun earlier later =>
        collation.compare (key.eval (Resolved.EvalContext.bound parameters) later)
          (key.eval (Resolved.EvalContext.bound parameters) earlier) ≠ .eq := by
  simp [keyGroupsShort, List.all_eq_true, Resolved.groups_short_iff_pairwise, Resolved.sameGroup_single,
    beq_eq_false_iff_ne]

#print axioms duplicateKeys_calm
#print axioms duplicateKeysOne_run
#print axioms noDuplicateKeys_claims
#print axioms keyGroupsShort_iff_pairwise
