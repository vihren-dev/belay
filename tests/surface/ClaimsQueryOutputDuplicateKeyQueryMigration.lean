import Belay.Sqlite.DuplicateKeyQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Holds.iff_selectOne_noDuplicateKeys.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {term : Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)} {position : Nat}
    {table : CatalogTable} {key : Resolved.Expr} {collation : Collation} {name : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none
      none [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] none [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (groupResolves : GroupTermResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0, aggregates := [.callStar name] } term key collation)
    (keyCalm : key.Calm) :
    Holds script db isQuery ↔
      ∀ group ∈ Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }), group.length ≤ 1 := by
  unfold Holds
  rw [Script.outputOn_noDuplicateKeys head count namedSource current arguments found groupResolves keyCalm]
  simp [Output.hasRows, apply_ite, List.all_eq_true]

-- Original Empty.iff_selectOne_noDuplicateKeys.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {term : Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)} {position : Nat}
    {table : CatalogTable} {key : Resolved.Expr} {collation : Collation} {name : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none
      none [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] none [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (groupResolves : GroupTermResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0, aggregates := [.callStar name] } term key collation)
    (keyCalm : key.Calm) :
    Empty script db isQuery ↔
      ∃ group ∈ Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }), 1 < group.length := by
  unfold Empty
  rw [Script.outputOn_noDuplicateKeys head count namedSource current arguments found groupResolves keyCalm]
  simp [Output.hasNoRows, apply_ite, List.all_eq_true, Nat.not_le]

-- Original Fails.not_selectOne_noDuplicateKeys.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {term : Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)} {position : Nat}
    {table : CatalogTable} {key : Resolved.Expr} {collation : Collation} {name : String}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none
      none [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] none [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none, parameters) :: rest)
    (count : normalizeIdentifier name = "count")
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (groupResolves : GroupTermResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0, aggregates := [.callStar name] } term key collation)
    (keyCalm : key.Calm) :
    ¬ Fails script db isQuery := by
  unfold Fails
  rw [Script.outputOn_noDuplicateKeys head count namedSource current arguments found groupResolves keyCalm]
  simp [Output.isError, apply_ite, List.all_eq_true]

end Belay.Sqlite
