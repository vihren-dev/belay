import Belay.Sqlite.QueryBridge
import Belay.Sqlite.Model

set_option doc.verso true

/-! The query form {lit}`SELECT 1 WHERE NOT EXISTS (SELECT c FROM t [WHERE w] GROUP BY k HAVING count(*) > 1)` over every
database (ADR 0017, S4 and S6): "no two rows of {lit}`t` for which {lit}`w` is true have a key {lit}`k` that is
equal". It is the general form of the query of {lit}`Belay/Sqlite/DuplicateKeyQuery.lean`, which has no {lit}`WHERE` and
the result column {lit}`1`. When the catalog of the database has the table, and {lit}`c`, {lit}`w` and {lit}`k` resolve in
the scope of the table to expressions that are calm (no fallible call, no clock read and no counter read), the claims
{lit}`Holds` and {lit}`Empty` of the query are statements about the groups that {lit}`GROUP BY` makes of the rows that
{lit}`WHERE` keeps, and {lit}`Fails` does not hold. A condition that can fail is not calm: the premises exclude it, so
these laws do not cover it and never read it as false. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

/-- For every script whose first statement is {lit}`SELECT 1 WHERE NOT EXISTS (SELECT c FROM t [WHERE w] GROUP BY k HAVING
count(*) > 1)`, where the catalog of the database has the table {lit}`t` at a position and {lit}`c`, {lit}`w` and
{lit}`k` resolve in the scope of the table ({name}`resolveQueryBody_duplicateKeys`), the output of the script is the
output of the step of the simple query without source whose condition is {lit}`NOT EXISTS` of subquery 0, with the
duplicate-key query of that table as its one subquery. The source reference has no indexed query. The table reference
names no schema: it is not a {lit}`before.t` source. Proof sketch: {name}`Script.outputOn_query` with the resolution of
{name}`resolveStatement_selectOne_notExists_duplicateKeys`. -/
theorem Script.outputOn_selectOne_noDuplicateKeysWhere
    {script : Script} {db : Database} {reference : Syntax.TableReference} {value : Syntax.Expr} {text : String}
    {filter : Option Syntax.Expr} {term : Syntax.Expr} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)} {position : Nat} {table : CatalogTable} {column : Resolved.Expr}
    {columnName : String} {affinity : Option Affinity} {key : Resolved.Expr} {collation : Collation}
    {whereCondition : Option Resolved.Expr} {name : String}
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
      (value.collationIn (tableScope db.raw.catalog reference position table)) term key collation) :
    script.outputOn db = some (resolvedStepOutput none 0 db.raw.connection parameters
      (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
        [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] whereCondition column columnName key
          collation])) :=
  Script.outputOn_query script db _ parameters rest _ _ _ head
    (resolveStatement_selectOne_notExists_duplicateKeys runContext db.raw.connection.resolveState reference value text
      filter term name count position table column columnName affinity key collation whereCondition namedSource current
      arguments found notCall noCalls columnResolves columnGrouped columnFeeds filterResolves groupResolves)

/-- For every script with the resolution premises of {name}`Script.outputOn_selectOne_noDuplicateKeysWhere`,
when the resolved expressions satisfy the stated calmness premises, its complete first output is
one row containing integer one when every key group of rows kept by the filter has at most
one row, and no rows otherwise. NULL keys group together under the resolved collation.
Proof sketch: resolve once, then substitute {name}`resolvedStepOutput_notExists_duplicateKeys`. -/
theorem Script.outputOn_noDuplicateKeysWhere
    {script : Script} {db : Database} {reference : Syntax.TableReference}
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
    script.outputOn db = some (.rows (if (Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.keptRows (Resolved.EvalContext.bound parameters) whereCondition (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }))).all
          (fun group => decide (group.length ≤ 1)) then [[.integer 1]] else [])) := by
  rw [Script.outputOn_selectOne_noDuplicateKeysWhere head count namedSource current arguments found notCall noCalls
    columnResolves columnGrouped columnFeeds filterResolves groupResolves]
  exact congrArg some (resolvedStepOutput_notExists_duplicateKeys 0 position db.raw.connection parameters
    { shape := table, rows := db.raw.rows.getD position [] } whereCondition column columnName key collation
    (Database.table_of_findTable db.raw _ position table found)
    (Resolved.Statement.Calm.selectOne_duplicateKeys position _ whereCondition column columnName key collation ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists 0)) whereCalm columnCalm keyCalm))

/-- For every script as in {name}`Script.outputOn_noDuplicateKeysWhere`: {name}`Holds` of the script on the
database means that no row that {lit}`WHERE` keeps has a key that compares as equal, under the collation, to the key
of a row that {lit}`WHERE` keeps before it in scan order. In words: no two rows for which the condition is true have
keys that compare as equal under the collation, and two NULL keys compare as equal. Proof sketch:
{name}`Script.outputOn_noDuplicateKeysWhere` and {name}`Resolved.groups_short_iff_pairwise` with
{name}`Resolved.sameGroup_single`. -/
theorem Holds.iff_selectOne_noDuplicateKeysWhere_pairwise
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
    Holds script db isQuery ↔
      (Resolved.keptRows (Resolved.EvalContext.bound parameters) whereCondition
        (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] })).Pairwise
        fun earlier later => collation.compare (key.eval (Resolved.EvalContext.bound parameters) later)
          (key.eval (Resolved.EvalContext.bound parameters) earlier) ≠ Ordering.eq := by
  simp [Holds, Script.outputOn_noDuplicateKeysWhere head count namedSource current arguments found notCall noCalls
    columnResolves columnGrouped columnFeeds filterResolves groupResolves whereCalm columnCalm keyCalm,
    Output.hasRows, apply_ite, Resolved.groups_short_iff_pairwise, Resolved.sameGroup_single,
    beq_eq_false_iff_ne]

end Belay.Sqlite
