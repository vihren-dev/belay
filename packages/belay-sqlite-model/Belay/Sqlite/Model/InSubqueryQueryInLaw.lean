import Belay.Sqlite.Model.InSubqueryQueryLaw

set_option doc.verso true

/-! The query law of {lit}`x IN (SELECT c FROM u)` against the correlated {lit}`EXISTS (SELECT 1 FROM u WHERE u.c = x)`
(task 20261027): the positive polarity of {name}`Belay.Sqlite.Model.resolvedStepOutput_notIn_eq_notExists`. It needs no
premise on NULL. -/

namespace Belay.Sqlite.Model

/-- **Query law of IN.** For every connection, values, outer table at a position and subquery table at a position of the
database, positions of the result columns, key position {lit}`key` inside the width {lit}`outer` of the outer cells, and
column {lit}`column` of the subquery table, the step of {lit}`SELECT p1, … FROM t WHERE x IN (SELECT c FROM u)` and the
step of {lit}`SELECT p1, … FROM t WHERE EXISTS (SELECT 1 FROM u WHERE u.c = x)` give rows, and the same rows ({lit}`Output.rows` of one list),
with any clock and index, under one premise: for every row of {lit}`t` with a key cell that is not NULL and every row of {lit}`u`, the
{lit}`IN` test and the comparison {lit}`=` match the cell equally ({name}`Belay.Sqlite.Model.Resolved.inMatches`;
{lit}`agree`). A NULL key cell or a NULL cell of {lit}`c` needs no premise: neither makes {lit}`IN` or {lit}`=` true. The
outputs are the rows of {lit}`t` that the condition keeps, in normal form ({name}`Belay.Sqlite.Model.Resolved.normalForm`). When {lit}`agree` fails, the statements can
differ. Proof sketch: as for {name}`resolvedStepOutput_notIn_eq_notExists`, with the filter law of {lit}`IN`
({name}`Resolved.Expr.evaluate_in_truthy_eq_exists_of_columns`). -/
theorem resolvedStepOutput_in_eq_exists (clock : Option Clock)
    (index outerPosition innerPosition outer column key : Nat) (connection : Connection) (parameters : List Value)
    (outerTable innerTable : Table) (columns : List Nat) (namesMain namesIn namesExists : List String)
    (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation) (keyInside : key < outer)
    (presentOuter : connection.state.database.table outerPosition = some outerTable)
    (presentInner : connection.state.database.table innerPosition = some innerTable)
    (agree : ∀ row ∈ Resolved.sourceRows outerTable, (row.getD key .null).isNull = false →
      ∀ cells ∈ Resolved.sourceRows innerTable,
      Resolved.inMatches inAffinity inCollation (row.getD key .null) (cells.getD column .null) =
        Resolved.inMatches equalsAffinity equalsCollation (row.getD key .null) (cells.getD column .null)) :
    ∃ rows : List (List Value), resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 inAffinity inCollation false)) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]) = .rows rows ∧
      resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0 (some (.exists 0)) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer
            (some (.compare .eq equalsAffinity (.column (outer + column)) (.column key) equalsCollation))
            [.literal (.integer 1)] namesExists]) = .rows rows := by
  have calmIn := Resolved.Query.inColumn_calm innerPosition outer column namesIn
  have calmExists := Resolved.Query.equalsColumn_calm innerPosition outer column key equalsAffinity equalsCollation
    namesExists
  have inCondition : ∀ expression ∈ (some (Resolved.Expr.inQuery (.column key) 0 inAffinity inCollation false)).toList,
      expression.Calm := fun expression member => by
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    exact (Resolved.Expr.calm_inQuery ..).mpr (Resolved.Expr.calm_column _)
  have existsCondition : ∀ expression ∈ (some (Resolved.Expr.exists 0)).toList, expression.Calm :=
    fun expression member => by
      simp only [Option.toList_some, List.mem_singleton] at member
      subst member
      exact Resolved.Expr.calm_exists 0
  have calmStatementIn := Resolved.Query.oneTable_calm outerPosition
    (some (.inQuery (.column key) 0 inAffinity inCollation false)) (columns.map .column) namesMain _ inCondition
    (fun expression member => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact Resolved.Expr.calm_column _) calmIn
  have calmStatementExists := Resolved.Query.oneTable_calm outerPosition (some (.exists 0))
    (columns.map .column) namesMain _ existsCondition
    (fun expression member => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact Resolved.Expr.calm_column _) calmExists
  have servedIn := fun row => connection.queryContext_subquery_zero parameters _ _ calmStatementIn row
  have servedExists := fun row => connection.queryContext_subquery_zero parameters _ _ calmStatementExists row
  have filterLaw : ∀ row ∈ Resolved.sourceRows outerTable, _ ∧ _ ∧ _ := fun row member =>
    Resolved.Expr.evaluate_in_truthy_eq_exists_of_columns _ _ (Resolved.EvalContext.bound parameters)
      connection.state.database none innerPosition outer column key inAffinity equalsAffinity inCollation
      equalsCollation namesIn namesExists innerTable row keyInside presentInner (servedIn row) (servedExists row)
      (agree row member)
  refine resolvedStepOutput_oneTable_congr clock index outerPosition connection parameters outerTable _ _ columns
    namesMain namesMain _ _ presentOuter inCondition existsCondition calmIn calmExists ?_ ?_ ?_
  · intro row _ expression inside
    simp only [Option.toList_some, List.mem_singleton] at inside
    subst inside
    exact Resolved.Expr.fault_inQuery_of_columns _ (Resolved.EvalContext.bound parameters) connection.state.database
      none innerPosition outer column key inAffinity inCollation false namesIn innerTable row presentInner
      (servedIn row)
  · intro row _ expression inside
    simp only [Option.toList_some, List.mem_singleton] at inside
    subst inside
    exact (Resolved.Expr.fault_exists_of_columns _ (Resolved.EvalContext.bound parameters)
      connection.state.database none innerPosition outer column key equalsAffinity equalsCollation namesExists
      innerTable row presentInner (servedExists row)).1
  · intro row member
    simp only [Resolved.conditionKeeps, Option.all_some, Resolved.Expr.eval, (filterLaw row member).1]

end Belay.Sqlite.Model
