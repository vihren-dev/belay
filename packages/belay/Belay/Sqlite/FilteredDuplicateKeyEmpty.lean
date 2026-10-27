import Belay.Sqlite.FilteredDuplicateKeyQuery

set_option doc.verso true

/-! The claims {lit}`Empty` and {lit}`Fails` of the query form of {lit}`Belay/Sqlite/FilteredDuplicateKeyQuery.lean`:
{lit}`Empty` means that two rows that {lit}`WHERE` keeps have keys that are equal under the collation, and {lit}`Fails`
never holds for a query whose expressions are calm. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script as in {name}`Holds.iff_selectOne_noDuplicateKeysWhere`: {name}`Empty` of the script on the
database means that some group of the rows that {lit}`WHERE` keeps, grouped by the key under the collation, has more
than one row: two such rows have keys that compare equal under the collation (two NULL keys compare equal). Proof
sketch: {name}`Script.outputOn_selectOne_noDuplicateKeysWhere` and
{name}`resolvedStepOutput_notExists_duplicateKeys_hasNoRows`. -/
theorem Empty.iff_selectOne_noDuplicateKeysWhere
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {value : Syntax.Expr} {text : String} {filter : Option Syntax.Expr} {term : Syntax.Expr}
    {parameters : List Value} {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {column : Resolved.Expr} {columnName : String} {affinity : Option Affinity} {key : Resolved.Expr}
    {collation : Collation} {whereCondition : Option Resolved.Expr} {name : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none
      none [Syntax.Subquery.mk [.expression value none text] (some reference) [] filter [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none, parameters) :: rest)
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
    (whereCalm : ∀ condition, whereCondition = some condition → condition.Calm) (columnCalm : column.Calm)
    (keyCalm : key.Calm) :
    Empty script db isQuery ↔
      ∃ group ∈ Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.keptRows (Resolved.EvalContext.bound parameters) whereCondition
          (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] })), 1 < group.length := by
  unfold Empty
  rw [Script.outputOn_selectOne_noDuplicateKeysWhere head count namedSource current arguments found notCall noCalls
    columnResolves columnGrouped columnFeeds filterResolves groupResolves, Option.any_some]
  exact resolvedStepOutput_notExists_duplicateKeys_hasNoRows 0 position db.raw.connection parameters
    { shape := table, rows := db.raw.rows.getD position [] } whereCondition column columnName key collation
    (Database.table_of_findTable db.raw _ position table found)
    (Resolved.Statement.Calm.selectOne_duplicateKeys position _ whereCondition column columnName key collation ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists 0)) whereCalm columnCalm keyCalm)

/-- For every script as in {name}`Holds.iff_selectOne_noDuplicateKeysWhere`, {name}`Fails` of the script on the
database does not hold: a calm query of a table that exists neither fails to resolve nor fails to run, so the
premise of calm expressions excludes a condition that can fail. The law says nothing about such a condition, and it is
never read as false. Proof sketch:
{name}`Script.outputOn_selectOne_noDuplicateKeysWhere` and
{name}`resolvedStepOutput_notExists_duplicateKeys_not_isError`. -/
theorem Fails.not_selectOne_noDuplicateKeysWhere
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {value : Syntax.Expr} {text : String} {filter : Option Syntax.Expr} {term : Syntax.Expr}
    {parameters : List Value} {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable}
    {column : Resolved.Expr} {columnName : String} {affinity : Option Affinity} {key : Resolved.Expr}
    {collation : Collation} {whereCondition : Option Resolved.Expr} {name : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none
      none [Syntax.Subquery.mk [.expression value none text] (some reference) [] filter [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none, parameters) :: rest)
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
    (whereCalm : ∀ condition, whereCondition = some condition → condition.Calm) (columnCalm : column.Calm)
    (keyCalm : key.Calm) :
    ¬ Fails script db isQuery := by
  unfold Fails
  rw [Script.outputOn_selectOne_noDuplicateKeysWhere head count namedSource current arguments found notCall noCalls
    columnResolves columnGrouped columnFeeds filterResolves groupResolves, Option.any_some,
    resolvedStepOutput_notExists_duplicateKeys_not_isError 0 position db.raw.connection parameters
    { shape := table, rows := db.raw.rows.getD position [] } whereCondition column columnName key collation
    (Database.table_of_findTable db.raw _ position table found)
    (Resolved.Statement.Calm.selectOne_duplicateKeys position _ whereCondition column columnName key collation ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists 0)) whereCalm columnCalm keyCalm)]
  simp

end Belay.Sqlite
