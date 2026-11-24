import SelectSyntaxFrame
import Belay

set_option doc.verso true

/-! Original observation contracts under ADR 0033. Successful resolution supplies the output evidence. -/

namespace Belay.Sqlite.ReplacedSubqueryEquivalence
open Belay.Sqlite.Model

/-- The former {lit}`Sql.EquivAt.in_exists_of_rowidAlias` follows at its original premises. -/
theorem Sql_EquivAt_in_exists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value} {afterFirst afterSecond : ResolveState}
    {firstStatement secondStatement : Syntax.Statement}
    (firstSelect : IsSelectStatement firstStatement) (secondSelect : IsSelectStatement secondStatement)
    (outerPosition innerPosition outer column key : Nat) (outerTable innerTable : Table) (columns : List Nat)
    (namesMain namesIn namesExists : List String) (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (keyInside : key < outer)
    (presentOuter : state.connection.state.database.table outerPosition = some outerTable)
    (presentInner : state.connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text)
    (firstStatements : first.statements = [(firstStatement, parameters)])
    (secondStatements : second.statements = [(secondStatement, parameters)])
    (firstResolves : resolveStatement runContext state.connection.resolveState
      firstStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation false)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn], afterFirst))
    (secondResolves : resolveStatement runContext state.connection.resolveState
      secondStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0 (some (.exists 0)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists], afterSecond)) :
    Sql.EquivAt (send first) (send second) state := by
  exact Sql.EquivAt.in_exists_of_rowidAlias (selectFrame firstSelect) (selectFrame secondSelect) outerPosition innerPosition outer column
    key outerTable innerTable columns namesMain namesIn namesExists affinity inCollation equalsCollation
    keyInside presentOuter presentInner alias aliased notText firstStatements secondStatements
    (runScriptStep_output_of_resolved firstResolves) (runScriptStep_output_of_resolved secondResolves)

#print axioms Sql_EquivAt_in_exists_of_rowidAlias

end Belay.Sqlite.ReplacedSubqueryEquivalence
