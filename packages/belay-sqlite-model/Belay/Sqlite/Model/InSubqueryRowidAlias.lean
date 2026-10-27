import Belay.Sqlite.Model.InSubqueryColumnLaw
import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-! The structural premises of the filter laws of {lit}`x NOT IN (SELECT c FROM u)` and {lit}`x IN (SELECT c FROM u)` (task 20261027). When {lit}`x` is a
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

/-- **Filter law of NOT IN under structural premises.** For one row {lit}`outerRow` of an outer table, a database with the
subquery table {lit}`u` at a position ({lit}`present`), a key position inside the width {lit}`outer` of the outer cells
({lit}`keyInside`), a context that serves subquery 0 with {lit}`SELECT c FROM u` ({lit}`servedIn`) and a context that
serves subquery 0 with {lit}`SELECT 1 FROM u WHERE u.c = x` ({lit}`servedExists`), both as {name}`Query.oneTable`, the
value and fault of {lit}`x NOT IN (SELECT c FROM u)` are those of {lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)`,
and the fault of both is none, under these premises:
* the key column is the rowid alias of the outer table ({lit}`alias`), every row of the outer table has its alias cell
  equal to its rowid ({lit}`aliased`: {name}`Table.RowsAliased`), and the outer row is a source row of the outer table
  ({lit}`member`); the key cell is then an integer;
* the one comparison affinity of the {lit}`IN` test and the comparison {lit}`=` is not TEXT ({lit}`notText`; it holds
  when the key column has INTEGER affinity, {name}`Belay.Sqlite.Model.comparisonAffinity_integer_ne_text`, and the two
  tests take the same affinity because {name}`Belay.Sqlite.Model.comparisonAffinity_comm` does not depend on the order of
  the operands);
* no cell of the column {lit}`c` is NULL in any row of {lit}`u` ({lit}`known`).

The two collations are free. The probe is never NULL and the two tests match the same candidates, so these two premises
of {name}`Expr.evaluate_notIn_eq_notExists_of_columns` need no assumption. When {lit}`known` fails and no row matches,
{lit}`NOT IN` is NULL and {lit}`NOT EXISTS` is 1. Proof sketch: the alias cell is an integer
({name}`sourceRows_alias_cell`), which is not NULL; for an integer probe the collation does not matter
({name}`inMatches_integer_collation_free`); apply {name}`Expr.evaluate_notIn_eq_notExists_of_columns`. -/
theorem Expr.evaluate_notIn_eq_notExists_of_rowidAlias (inContext existsContext inner : EvalContext)
    (database : Database) (initial : Option Database) (position outer column key : Nat)
    (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (namesIn namesExists : List String) (table outerTable : Table) (outerRow : List Value)
    (present : database.table position = some table)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (member : outerRow ∈ sourceRows outerTable) (notText : affinity ≠ some .text)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer none [.column (outer + column)] namesIn).subqueryRun inner database outerRow
        initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer (some (.compare .eq affinity (.column (outer + column)) (.column key)
        equalsCollation)) [.literal (.integer 1)] namesExists).subqueryRun inner database outerRow initial)
    (keyInside : key < outer)
    (known : ∀ cells ∈ sourceRows table, (cells.getD column .null).isNull = false) :
    (Expr.inQuery (.column key) 0 affinity inCollation true).evaluate inContext outerRow =
        (Expr.not (.exists 0)).evaluate existsContext outerRow ∧
      ((Expr.inQuery (.column key) 0 affinity inCollation true).evaluate inContext outerRow).2 = .none := by
  obtain ⟨number, integer⟩ := sourceRows_alias_cell outerTable key alias aliased outerRow member
  refine Expr.evaluate_notIn_eq_notExists_of_columns inContext existsContext inner database initial position
    outer column key affinity affinity inCollation equalsCollation namesIn namesExists table outerRow
    keyInside present servedIn servedExists (by rw [integer]; rfl) known ?_
  intro cells _
  rw [integer]
  exact inMatches_integer_collation_free notText inCollation equalsCollation number _

/-- **Filter law of IN under structural premises.** For the same outer row, contexts and database as in
{name}`Expr.evaluate_notIn_eq_notExists_of_rowidAlias`, with {lit}`IN` and {lit}`EXISTS`, the truth of
{lit}`x IN (SELECT c FROM u)` is the truth of {lit}`EXISTS (SELECT 1 FROM u WHERE u.c = x)`, and neither has a fault,
under the premises {lit}`alias`, {lit}`aliased`, {lit}`member` and {lit}`notText`. It needs no premise on NULL cells of
{lit}`c`: a NULL cell never matches. The collations are free. Proof sketch: the alias cell is an integer
({name}`sourceRows_alias_cell`) and the collation does not matter for it ({name}`inMatches_integer_collation_free`);
apply {name}`Expr.evaluate_in_truthy_eq_exists_of_columns`. -/
theorem Expr.evaluate_in_truthy_eq_exists_of_rowidAlias (inContext existsContext inner : EvalContext)
    (database : Database) (initial : Option Database) (position outer column key : Nat)
    (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (namesIn namesExists : List String) (table outerTable : Table) (outerRow : List Value)
    (present : database.table position = some table)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (member : outerRow ∈ sourceRows outerTable) (notText : affinity ≠ some .text)
    (servedIn : inContext.subqueries 0 outerRow =
      (Query.oneTable position outer none [.column (outer + column)] namesIn).subqueryRun inner database outerRow
        initial)
    (servedExists : existsContext.subqueries 0 outerRow =
      (Query.oneTable position outer (some (.compare .eq affinity (.column (outer + column)) (.column key)
        equalsCollation)) [.literal (.integer 1)] namesExists).subqueryRun inner database outerRow initial)
    (keyInside : key < outer) :
    truthy ((Expr.inQuery (.column key) 0 affinity inCollation false).evaluate inContext outerRow).1 =
        truthy ((Expr.exists 0).evaluate existsContext outerRow).1 ∧
      ((Expr.inQuery (.column key) 0 affinity inCollation false).evaluate inContext outerRow).2 = .none ∧
      ((Expr.exists 0).evaluate existsContext outerRow).2 = .none := by
  obtain ⟨number, integer⟩ := sourceRows_alias_cell outerTable key alias aliased outerRow member
  refine Expr.evaluate_in_truthy_eq_exists_of_columns inContext existsContext inner database initial position
    outer column key affinity affinity inCollation equalsCollation namesIn namesExists table outerRow
    keyInside present servedIn servedExists ?_
  intro _ cells _
  rw [integer]
  exact inMatches_integer_collation_free notText inCollation equalsCollation number _

end Belay.Sqlite.Model.Resolved
