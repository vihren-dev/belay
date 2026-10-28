import Belay.Sqlite.NotExistsQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Holds.iff_selectOne_notExists.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none none
      [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] subFilter [] [] none none none none false none none]
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (calm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    Holds script db isQuery ↔
      ∀ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
        subCondition.all (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = false := by
  unfold Holds
  rw [Script.outputOn_notExists head namedSource current arguments found resolves calm]
  simp [Output.hasRows, apply_ite, List.any_eq_false]

-- Original Empty.iff_selectOne_notExists.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none none
      [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] subFilter [] [] none none none none false none none]
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (calm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    Empty script db isQuery ↔
      ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
        subCondition.all (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = true := by
  unfold Empty
  rw [Script.outputOn_notExists head namedSource current arguments found resolves calm]
  simp [Output.hasNoRows, apply_ite, List.any_eq_false]

-- Original Fails.not_selectOne_notExists.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {subFilter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none none
      [Syntax.Subquery.mk [.expression (.numeric "1") none "1"] (some reference) [] subFilter [] [] none none none none false none none]
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none) (found : db.raw.catalog.findTable reference.table = some (position, table))
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (calm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    ¬ Fails script db isQuery := by
  unfold Fails
  rw [Script.outputOn_notExists head namedSource current arguments found resolves calm]
  simp [Output.isError, apply_ite, List.any_eq_false]

end Belay.Sqlite
