import Belay.Sqlite.FilteredDuplicateKeyQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Empty.iff_selectOne_noDuplicateKeysWhere.
example
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
  rw [Script.outputOn_noDuplicateKeysWhere head count namedSource current arguments found notCall noCalls columnResolves columnGrouped columnFeeds filterResolves groupResolves whereCalm columnCalm keyCalm]
  simp [Output.hasNoRows, apply_ite, List.all_eq_true, Nat.not_le]

-- Original Fails.not_selectOne_noDuplicateKeysWhere.
example
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
  rw [Script.outputOn_noDuplicateKeysWhere head count namedSource current arguments found notCall noCalls columnResolves columnGrouped columnFeeds filterResolves groupResolves whereCalm columnCalm keyCalm]
  simp [Output.isError, apply_ite, List.all_eq_true]

end Belay.Sqlite
