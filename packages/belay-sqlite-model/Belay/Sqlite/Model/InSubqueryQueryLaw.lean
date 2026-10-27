import Belay.Sqlite.Model.OneTableStatementOutput
import Belay.Sqlite.Model.InSubqueryColumnLaw

set_option doc.verso true

/-! The query laws of {lit}`x IN (SELECT c FROM u)` and {lit}`x NOT IN (SELECT c FROM u)` against the correlated
{lit}`EXISTS` and {lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` (task 20261027): two statements of the form
{lit}`SELECT p1, p2, … FROM t WHERE condition` with one subquery, whose condition is the first or the second form, give
the same output when the premises of the filter law hold for every row of the outer table. The result columns are
columns of the outer table, so they do not depend on the subquery. -/

namespace Belay.Sqlite.Model

/-- The expressions of the subquery {lit}`SELECT c FROM u` of an {lit}`IN` test are calm
({name}`Resolved.Expr.Calm`). Proof sketch: the one expression is a column ({name}`Resolved.Expr.calm_column`). -/
theorem Resolved.Query.inColumn_calm (table outer column : Nat) (names : List String) :
    ∀ expression ∈ (Resolved.Query.oneTable table outer none [.column (outer + column)] names).expressions,
      expression.Calm := by
  intro expression member
  rw [Resolved.Query.oneTable_expressions] at member
  simp only [Option.toList_none, List.nil_append, List.mem_singleton] at member
  subst member
  exact Resolved.Expr.calm_column _

/-- The expressions of the correlated subquery {lit}`SELECT 1 FROM u WHERE u.c = x` are calm. Proof sketch: they are a
comparison of two columns ({name}`Resolved.Expr.calm_compare`) and a literal. -/
theorem Resolved.Query.equalsColumn_calm (table outer column key : Nat) (affinity : Option Affinity)
    (collation : Collation) (names : List String) :
    ∀ expression ∈ (Resolved.Query.oneTable table outer
      (some (.compare .eq affinity (.column (outer + column)) (.column key) collation)) [.literal (.integer 1)]
      names).expressions, expression.Calm := by
  intro expression member
  rw [Resolved.Query.oneTable_expressions] at member
  simp only [Option.toList_some, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl
  · exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column _, Resolved.Expr.calm_column _⟩
  · exact Resolved.Expr.calm_literal _

/-- **Query law of NOT IN.** For every connection, values, outer table at a position and subquery table at a position
of the database, positions of the result columns, key position {lit}`key` inside the width {lit}`outer` of the outer
cells, and column {lit}`column` of the subquery table, the step of
{lit}`SELECT p1, … FROM t WHERE x NOT IN (SELECT c FROM u)` and the step of
{lit}`SELECT p1, … FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` give the same output with any clock and
index, under these premises:
* the key cell of every row of {lit}`t` is not NULL ({lit}`probe`);
* the cell of the column {lit}`c` is not NULL in any row of {lit}`u` ({lit}`known`);
* for every row of {lit}`t` and every row of {lit}`u`, the {lit}`IN` test and the comparison {lit}`=` match the cell
  equally ({name}`Belay.Sqlite.Model.Resolved.inMatches`; {lit}`agree`).

The two outputs are rows of the same cells in the same order: the rows of {lit}`t` in scan order that the condition
keeps. When {lit}`probe` fails for a row and {lit}`u` has a row, {lit}`NOT IN` is NULL, so the first statement drops the
row, and {lit}`NOT EXISTS` is true, so the second keeps it, because {lit}`=` with a NULL operand is never true. When
{lit}`known` fails and no row matches, the first statement drops the row and the second keeps it. When {lit}`agree`
fails, the statements can differ too. Proof sketch: {name}`resolvedStepOutput_oneTable_congr` reduces the claim to the
conditions keeping the same rows without fault; the filter law
({name}`Resolved.Expr.evaluate_notIn_eq_notExists_of_columns`) gives that for each row of {lit}`t`, in the contexts that
serve the subqueries ({name}`Connection.queryContext_subquery_zero`). -/
theorem resolvedStepOutput_notIn_eq_notExists (clock : Option Clock)
    (index outerPosition innerPosition outer column key : Nat) (connection : Connection) (parameters : List Value)
    (outerTable innerTable : Table) (columns : List Nat) (namesMain namesIn namesExists : List String)
    (inAffinity equalsAffinity : Option Affinity) (inCollation equalsCollation : Collation) (keyInside : key < outer)
    (presentOuter : connection.state.database.table outerPosition = some outerTable)
    (presentInner : connection.state.database.table innerPosition = some innerTable)
    (probe : ∀ row ∈ Resolved.sourceRows outerTable, (row.getD key .null).isNull = false)
    (known : ∀ cells ∈ Resolved.sourceRows innerTable, (cells.getD column .null).isNull = false)
    (agree : ∀ row ∈ Resolved.sourceRows outerTable, ∀ cells ∈ Resolved.sourceRows innerTable,
      Resolved.inMatches inAffinity inCollation (row.getD key .null) (cells.getD column .null) =
        Resolved.inMatches equalsAffinity equalsCollation (row.getD key .null) (cells.getD column .null)) :
    resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 inAffinity inCollation true)) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]) =
      resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0 (some (.not (.exists 0))) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer
            (some (.compare .eq equalsAffinity (.column (outer + column)) (.column key) equalsCollation))
            [.literal (.integer 1)] namesExists]) := by
  have calmIn := Resolved.Query.inColumn_calm innerPosition outer column namesIn
  have calmExists := Resolved.Query.equalsColumn_calm innerPosition outer column key equalsAffinity equalsCollation
    namesExists
  have inCondition : ∀ expression ∈ (some (Resolved.Expr.inQuery (.column key) 0 inAffinity inCollation true)).toList,
      expression.Calm := fun expression member => by
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    exact (Resolved.Expr.calm_inQuery ..).mpr (Resolved.Expr.calm_column _)
  have existsCondition : ∀ expression ∈ (some (Resolved.Expr.not (.exists 0))).toList, expression.Calm :=
    fun expression member => by
      simp only [Option.toList_some, List.mem_singleton] at member
      subst member
      exact (Resolved.Expr.calm_not _).mpr (Resolved.Expr.calm_exists 0)
  have calmStatementIn := Resolved.Query.oneTable_calm outerPosition
    (some (.inQuery (.column key) 0 inAffinity inCollation true)) (columns.map .column) namesMain _ inCondition
    (fun expression member => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact Resolved.Expr.calm_column _) calmIn
  have calmStatementExists := Resolved.Query.oneTable_calm outerPosition (some (.not (.exists 0)))
    (columns.map .column) namesMain _ existsCondition
    (fun expression member => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact Resolved.Expr.calm_column _) calmExists
  have servedIn := fun row => connection.queryContext_subquery_zero parameters _ _ calmStatementIn row
  have servedExists := fun row => connection.queryContext_subquery_zero parameters _ _ calmStatementExists row
  have filterLaw : ∀ row ∈ Resolved.sourceRows outerTable, _ ∧ _ := fun row member =>
    Resolved.Expr.evaluate_notIn_eq_notExists_of_columns _ _ (Resolved.EvalContext.bound parameters)
      connection.state.database none innerPosition outer column key inAffinity equalsAffinity inCollation
      equalsCollation namesIn namesExists innerTable row keyInside presentInner (servedIn row) (servedExists row)
      (probe row member) known (agree row member)
  refine resolvedStepOutput_oneTable_congr clock index outerPosition connection parameters outerTable _ _ columns
    namesMain namesMain _ _ presentOuter inCondition existsCondition calmIn calmExists ?_ ?_ ?_
  · intro row _ expression inside
    simp only [Option.toList_some, List.mem_singleton] at inside
    subst inside
    exact Resolved.Expr.fault_inQuery_of_columns _ (Resolved.EvalContext.bound parameters) connection.state.database
      none innerPosition outer column key inAffinity inCollation true namesIn innerTable row presentInner
      (servedIn row)
  · intro row _ expression inside
    simp only [Option.toList_some, List.mem_singleton] at inside
    subst inside
    exact (Resolved.Expr.fault_exists_of_columns _ (Resolved.EvalContext.bound parameters)
      connection.state.database none innerPosition outer column key equalsAffinity equalsCollation namesExists
      innerTable row presentInner (servedExists row)).2
  · intro row member
    simp only [Resolved.conditionKeeps, Option.all_some, Resolved.Expr.eval, (filterLaw row member).1]

end Belay.Sqlite.Model
