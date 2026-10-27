import Belay.Sqlite.Model.NotInFilterLaw
import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-! The structural premises of the filter law of {lit}`x NOT IN (SELECT c FROM u)` (task 20261027). When {lit}`x` is a
rowid alias of the outer table, the key cell of every outer row is an integer, and for an integer probe the
{lit}`IN` test and the correlated comparison match the same candidates, whatever type, affinity and collation the
candidates have ({name}`Belay.Sqlite.Model.Resolved.inMatches_integer_collation_free`). So the premises that the filter law needs
for the key are checkable facts about the outer table; the remaining premise is that no cell of the column {lit}`c`
is NULL. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every table with a rowid alias at a position, whose rows all have their alias cell equal to their rowid
({name}`Table.RowsAliased`), and every row of the table as a source row ({name}`sourceRows`): the cell at the position
is an integer. Proof sketch: the source row is the values of a row of the table (the scan order permutes the rows,
{name}`Table.scanRows_perm`), and the alias cell of that row is its rowid. -/
theorem sourceRows_alias_cell (table : Table) (position : Nat) (alias : table.shape.rowidAlias = some position)
    (aliased : table.RowsAliased) (row : List Value) (member : row ∈ sourceRows table) :
    ∃ number : Int, row.getD position .null = .integer number := by
  obtain ⟨found, inScan, rfl⟩ := List.mem_map.mp member
  have inRows := table.scanRows_perm.subset inScan
  have cell := aliased found inRows position alias
  exact ⟨found.rowid, by simp [List.getD_eq_getElem?_getD, cell]⟩

/-- **Filter law under structural premises.** For one row of the outer table whose key column is its rowid alias
({lit}`alias`, {lit}`aliased`, {lit}`member`), and the one comparison affinity of the {lit}`IN` test and the comparison
{lit}`=`, which is not TEXT ({lit}`notText`; it holds when the key column has INTEGER affinity,
{name}`Belay.Sqlite.Model.comparisonAffinity_integer_ne_text`, and the two tests take the same affinity because
{name}`Belay.Sqlite.Model.comparisonAffinity_comm` does not depend on the order of the operands), the value and fault of {lit}`x NOT IN (SELECT c FROM u)` are those of
{lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)`, for any two collations, if no cell of the column {lit}`c` is NULL in
any row of {lit}`u` ({lit}`known`). The probe is never NULL and the two tests match the same candidates, so these two premises of
{name}`Expr.evaluate_notIn_eq_notExists` need no assumption. When {lit}`known` fails and no row matches, {lit}`NOT IN` is NULL and
{lit}`NOT EXISTS` is 1. Proof sketch: the alias cell is an integer ({name}`sourceRows_alias_cell`), which is not NULL;
for an integer probe the collation does not matter ({name}`inMatches_integer_collation_free`); apply
{name}`Expr.evaluate_notIn_eq_notExists`. -/
theorem Expr.evaluate_notIn_eq_notExists_of_rowidAlias (inContext existsContext innerIn innerExists : EvalContext)
    (database : Database) (initial : Option Database) (position outer column key : Nat)
    (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (namesIn namesExists : List String) (table outerTable : Table) (outerRow : List Value)
    (present : database.table position = some table)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (member : outerRow ∈ sourceRows outerTable) (notText : affinity ≠ some .text)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.columnOf position outer column namesIn).subqueryRun innerIn database outerRow initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.matchingKey position outer column key affinity equalsCollation namesExists).subqueryRun
        innerExists database outerRow initial)
    (keyInside : key < outer)
    (known : ∀ cells ∈ sourceRows table, (cells.getD column .null).isNull = false) :
    (Expr.inQuery (.column key) 0 affinity inCollation true).evaluate inContext outerRow =
      (Expr.not (.exists 0)).evaluate existsContext outerRow := by
  obtain ⟨number, integer⟩ := sourceRows_alias_cell outerTable key alias aliased outerRow member
  refine Expr.evaluate_notIn_eq_notExists inContext existsContext innerIn innerExists database initial position
    outer column key affinity affinity inCollation equalsCollation namesIn namesExists table outerRow
    keyInside present servedIn servedExists (by rw [integer]; rfl) known ?_
  intro cells _
  rw [integer]
  exact inMatches_integer_collation_free notText inCollation equalsCollation number _

end Belay.Sqlite.Model.Resolved
