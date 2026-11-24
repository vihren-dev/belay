import Belay

set_option doc.verso true

/-! Original observation contracts under ADR 0033. Successful resolution supplies the output evidence. -/

namespace Belay.Sqlite.ReplacedSubqueryEquivalence
open Belay.Sqlite.Model

/-- The original SELECT syntax supplies the frame for both a query and a prepare error. -/
private theorem selectFrame {statement : Syntax.Statement} (select : IsSelectStatement statement)
    {clock : Option Clock} {index : Nat} {conn : Connection} {values : List Value} :
    ∀ output next others, runScriptStep runContext clock index conn statement values = .continued output next others →
      others = [] ∧ next = conn := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := select
  exact fun _ _ _ => runScriptStep_select_keeps

/-- The former {lit}`Sql.EquivAt.notIn_notExists_of_rowidAlias` follows at its original premises. -/
theorem Sql_EquivAt_notIn_notExists_of_rowidAlias {first second : Script} {state : ExecutionContext}
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
    (known : ∀ cells ∈ Resolved.sourceRows innerTable, (cells.getD column .null).isNull = false)
    (firstStatements : first.statements = [(firstStatement, parameters)])
    (secondStatements : second.statements = [(secondStatement, parameters)])
    (firstResolves : resolveStatement runContext state.connection.resolveState
      firstStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation true)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn], afterFirst))
    (secondResolves : resolveStatement runContext state.connection.resolveState
      secondStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0 (some (.not (.exists 0))) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists], afterSecond)) :
    Sql.EquivAt (send first) (send second) state := by
  exact Sql.EquivAt.notIn_notExists_of_rowidAlias (selectFrame firstSelect) (selectFrame secondSelect) outerPosition innerPosition outer
    column key outerTable innerTable columns namesMain namesIn namesExists affinity inCollation equalsCollation
    keyInside presentOuter presentInner alias aliased notText known firstStatements secondStatements
    (runScriptStep_output_of_resolved firstResolves) (runScriptStep_output_of_resolved secondResolves)

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

#print axioms Sql_EquivAt_notIn_notExists_of_rowidAlias
#print axioms Sql_EquivAt_in_exists_of_rowidAlias

/-- Recover the earlier syntax and output premise from the two SELECT frames. -/
theorem original_frame_notIn_notExists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value}
    {firstStatement secondStatement : Syntax.Statement}
    (firstSelect : IsSelectStatement firstStatement) (secondSelect : IsSelectStatement secondStatement)
    (outerPosition innerPosition outer column key : Nat) (outerTable innerTable : Table) (columns : List Nat)
    (namesMain namesIn namesExists : List String) (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (keyInside : key < outer)
    (presentOuter : state.connection.state.database.table outerPosition = some outerTable)
    (presentInner : state.connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text)
    (known : ∀ cells ∈ Resolved.sourceRows innerTable, (cells.getD column .null).isNull = false)
    (firstStatements : first.statements = [(firstStatement, parameters)])
    (secondStatements : second.statements = [(secondStatement, parameters)])
    (firstOutput : (runScriptStep runContext state.clock state.index state.connection firstStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation true)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]))
    (secondOutput : (runScriptStep runContext state.clock state.index state.connection secondStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0 (some (.not (.exists 0))) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists])) :
    Sql.EquivAt (send first) (send second) state :=
  Sql.EquivAt.notIn_notExists_of_rowidAlias (selectFrame firstSelect) (selectFrame secondSelect)
    outerPosition innerPosition outer column key outerTable innerTable columns namesMain namesIn namesExists
    affinity inCollation equalsCollation keyInside presentOuter presentInner alias aliased notText known firstStatements secondStatements firstOutput secondOutput

#print axioms original_frame_notIn_notExists_of_rowidAlias

/-- Recover the earlier syntax and output premise from the two SELECT frames. -/
theorem original_frame_in_exists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value}
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
    (firstOutput : (runScriptStep runContext state.clock state.index state.connection firstStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation false)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]))
    (secondOutput : (runScriptStep runContext state.clock state.index state.connection secondStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0 (some (.exists 0)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists])) :
    Sql.EquivAt (send first) (send second) state :=
  Sql.EquivAt.in_exists_of_rowidAlias (selectFrame firstSelect) (selectFrame secondSelect)
    outerPosition innerPosition outer column key outerTable innerTable columns namesMain namesIn namesExists
    affinity inCollation equalsCollation keyInside presentOuter presentInner alias aliased notText firstStatements secondStatements firstOutput secondOutput

#print axioms original_frame_in_exists_of_rowidAlias

end Belay.Sqlite.ReplacedSubqueryEquivalence
