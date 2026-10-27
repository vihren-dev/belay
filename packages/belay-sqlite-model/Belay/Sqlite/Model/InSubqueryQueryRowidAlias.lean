import Belay.Sqlite.Model.InSubqueryQueryLaw
import Belay.Sqlite.Model.InSubqueryQueryInLaw
import Belay.Sqlite.Model.InSubqueryRowidAlias

set_option doc.verso true

/-! The query law of {lit}`x NOT IN (SELECT c FROM u)` under structural premises (task 20261027): when the key column
{lit}`x` is the rowid alias of the outer table, the statement with {lit}`NOT IN` and the statement with the correlated
{lit}`NOT EXISTS` give the same output if no cell of the column {lit}`c` is NULL. The premises are facts that a user can
check about a database, not facts about its values. -/

namespace Belay.Sqlite.Model

/-- **Query law under structural premises.** For every connection, values, outer table at a position and subquery
table at a position of the database, positions of the result columns, key position {lit}`key` inside the width
{lit}`outer` and column {lit}`column` of the subquery table, the step of
{lit}`SELECT p1, … FROM t WHERE x NOT IN (SELECT c FROM u)` and the step of
{lit}`SELECT p1, … FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` give the same output with any clock and
index, under these premises:
* the key column is the rowid alias of the outer table ({lit}`alias`), and every row of the outer table has its alias
  cell equal to its rowid ({lit}`aliased`: {name}`Table.RowsAliased`); the key cell of every row is then an integer;
* the one comparison affinity of the {lit}`IN` test and the comparison {lit}`=` is not TEXT ({lit}`notText`; it holds when
  the key column has INTEGER affinity, {name}`Belay.Sqlite.Model.comparisonAffinity_integer_ne_text`, and the two tests
  take the same affinity because {name}`Belay.Sqlite.Model.comparisonAffinity_comm` does not depend on the order of the
  operands);
* no cell of the column {lit}`c` is NULL in any row of {lit}`u` ({lit}`known`).

The two collations are free. When {lit}`known` fails, the statements can differ: a NULL cell makes {lit}`NOT IN` NULL for
every row without a match, and {lit}`NOT EXISTS` is then true. Proof sketch: the key cell is an integer, so it is not
NULL ({name}`Resolved.sourceRows_alias_cell`) and the two tests match the same cells whatever the collations are
({name}`Resolved.inMatches_integer_collation_free`); apply {name}`resolvedStepOutput_notIn_eq_notExists`. -/
theorem resolvedStepOutput_notIn_eq_notExists_of_rowidAlias (clock : Option Clock)
    (index outerPosition innerPosition outer column key : Nat) (connection : Connection) (parameters : List Value)
    (outerTable innerTable : Table) (columns : List Nat) (namesMain namesIn namesExists : List String)
    (affinity : Option Affinity) (inCollation equalsCollation : Collation) (keyInside : key < outer)
    (presentOuter : connection.state.database.table outerPosition = some outerTable)
    (presentInner : connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text)
    (known : ∀ cells ∈ Resolved.sourceRows innerTable, (cells.getD column .null).isNull = false) :
    resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation true)) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]) =
      resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0 (some (.not (.exists 0))) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer
            (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
            [.literal (.integer 1)] namesExists]) := by
  refine resolvedStepOutput_notIn_eq_notExists clock index outerPosition innerPosition outer column key connection
    parameters outerTable innerTable columns namesMain namesIn namesExists affinity affinity inCollation equalsCollation
    keyInside presentOuter presentInner ?_ known ?_
  · intro row member
    obtain ⟨number, integer⟩ := Resolved.sourceRows_alias_cell outerTable key alias aliased row member
    rw [integer]
    rfl
  · intro row member cells _
    obtain ⟨number, integer⟩ := Resolved.sourceRows_alias_cell outerTable key alias aliased row member
    rw [integer]
    exact Resolved.inMatches_integer_collation_free notText inCollation equalsCollation number _

/-- **Query law of IN under structural premises.** For the same connection, tables, columns and key as in
{name}`resolvedStepOutput_notIn_eq_notExists_of_rowidAlias`, the step of
{lit}`SELECT p1, … FROM t WHERE x IN (SELECT c FROM u)` and the step of
{lit}`SELECT p1, … FROM t WHERE EXISTS (SELECT 1 FROM u WHERE u.c = x)` give the same output with any clock and index,
under the premises {lit}`alias`, {lit}`aliased` and {lit}`notText`. It needs no premise on NULL cells of {lit}`c`, and the
collations are free. Proof sketch: the key cell is an integer ({name}`Resolved.sourceRows_alias_cell`), so the two
tests match the same cells ({name}`Resolved.inMatches_integer_collation_free`); apply
{name}`resolvedStepOutput_in_eq_exists`. -/
theorem resolvedStepOutput_in_eq_exists_of_rowidAlias (clock : Option Clock)
    (index outerPosition innerPosition outer column key : Nat) (connection : Connection) (parameters : List Value)
    (outerTable innerTable : Table) (columns : List Nat) (namesMain namesIn namesExists : List String)
    (affinity : Option Affinity) (inCollation equalsCollation : Collation) (keyInside : key < outer)
    (presentOuter : connection.state.database.table outerPosition = some outerTable)
    (presentInner : connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text) :
    resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation false)) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]) =
      resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable outerPosition 0 (some (.exists 0)) (columns.map .column) namesMain)
          [Resolved.Query.oneTable innerPosition outer
            (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
            [.literal (.integer 1)] namesExists]) := by
  refine resolvedStepOutput_in_eq_exists clock index outerPosition innerPosition outer column key connection
    parameters outerTable innerTable columns namesMain namesIn namesExists affinity affinity inCollation
    equalsCollation keyInside presentOuter presentInner ?_
  intro row member _ cells _
  obtain ⟨number, integer⟩ := Resolved.sourceRows_alias_cell outerTable key alias aliased row member
  rw [integer]
  exact Resolved.inMatches_integer_collation_free notText inCollation equalsCollation number _

end Belay.Sqlite.Model
