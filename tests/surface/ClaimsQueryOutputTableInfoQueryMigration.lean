import Belay.Sqlite.TableInfoQuery

set_option doc.verso true

/-! Temporary exact baseline formulas for D1; retire after final contract acceptance. -/

namespace Belay.Sqlite
open Belay.Sqlite.Model

-- Original Holds.iff_selectOne_tableInfo.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {argument : List UInt8} {rows : List (List Value)} {condition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none []
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : db.raw.catalog.findTable reference.table = none)
    (notView : db.raw.catalog.findView reference.table = none)
    (info : db.raw.catalog.tableInfoRows ⟨argument⟩ = some rows)
    (resolves : FilterResolves runContext.profile.dqsDml (tableInfoScope reference argument rows) [] filter condition)
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    Holds script db isQuery ↔
      ∃ row ∈ rows.map (· ++ [Value.text argument, Value.null]), condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = true := by
  unfold Holds
  rw [Script.outputOn_tableInfo head namedSource current arguments isFunction notTable notView info resolves calm]
  simp only [Option.any_some, Output.hasRows, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq,
    Resolved.normalForm_eq_nil, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    Classical.not_forall, Classical.not_not, exists_prop]

-- Original Empty.iff_selectOne_tableInfo.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {argument : List UInt8} {rows : List (List Value)} {condition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none []
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : db.raw.catalog.findTable reference.table = none)
    (notView : db.raw.catalog.findView reference.table = none)
    (info : db.raw.catalog.tableInfoRows ⟨argument⟩ = some rows)
    (resolves : FilterResolves runContext.profile.dqsDml (tableInfoScope reference argument rows) [] filter condition)
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    Empty script db isQuery ↔
      ∀ row ∈ rows.map (· ++ [Value.text argument, Value.null]), condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)) = false := by
  unfold Empty
  rw [Script.outputOn_tableInfo head namedSource current arguments isFunction notTable notView info resolves calm]
  simp only [Option.any_some, Output.hasNoRows, List.isEmpty_iff, Resolved.normalForm_eq_nil,
    List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true]

-- Original Fails.not_selectOne_tableInfo.
example
    {script : Script} {db : Database} {isQuery : script.isQuery = true} {reference : Syntax.TableReference}
    {filter : Option Syntax.Expr} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {argument : List UInt8} {rows : List (List Value)} {condition : Option Resolved.Expr}
    (head : script.statements = (.select [.expression (.numeric "1") none "1"] (some reference) [] filter [] [] none none []
      none false none, parameters) :: rest)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : db.raw.catalog.findTable reference.table = none)
    (notView : db.raw.catalog.findView reference.table = none)
    (info : db.raw.catalog.tableInfoRows ⟨argument⟩ = some rows)
    (resolves : FilterResolves runContext.profile.dqsDml (tableInfoScope reference argument rows) [] filter condition)
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    ¬ Fails script db isQuery := by
  unfold Fails
  rw [Script.outputOn_tableInfo head namedSource current arguments isFunction notTable notView info resolves calm]
  simp [Output.isError]

end Belay.Sqlite
