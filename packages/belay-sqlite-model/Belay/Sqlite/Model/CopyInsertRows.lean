import Belay.Sqlite.Model.SimpleResultsLaws
import Belay.Sqlite.Model.InsertSelectRun
import Belay.Sqlite.Model.DatabaseFacts

set_option doc.verso true

/-! The rows of a copying INSERT from a query (ADR 0017, S6). A query that selects every column of a table in order
hands over the rows of the table, and an INSERT that takes these columns in order writes the same cells when they
are already in the stored form of the target. -/

namespace Belay.Sqlite.Model

/-- For every list of columns and every second list with the same affinities, in order, and every row that is
stored in the form of the second list ({name}`Row.Stored`): the row is stored in the form of the first list. In plain
words, whether a cell is in stored form depends on the affinity of its column only. Proof sketch: the column at a
position of the first list has the affinity that the second list gives at the position. -/
theorem Row.Stored.of_affinities {columns other : List CatalogColumn} {row : Row}
    (same : columns.map CatalogColumn.affinity = other.map CatalogColumn.affinity) (stored : row.Stored other) :
    row.Stored columns := by
  intro position column value atColumn atValue
  have mapped := congrArg (·[position]?) same
  simp only [List.getElem?_map, atColumn, Option.map_some] at mapped
  obtain ⟨partner, atPartner, affinity⟩ := Option.map_eq_some_iff.mp mapped.symm
  rw [← affinity]
  exact stored position partner value atPartner atValue

/-- A cell at a position inside a row is the cell that {name}`List.getD` reads there. -/
private theorem getElem?_eq_some_getD (row : List Value) (position : Nat) (inside : position < row.length) :
    row[position]? = some (row.getD position .null) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  rfl

/-- For every simple query without {lit}`WHERE` whose result columns are the first {lit}`width` columns of its
source, in order, every context and every rows that have {lit}`width` cells: the result rows of the query are
the rows. In plain words, {lit}`SELECT a, b, c FROM t` hands over the rows of {lit}`t` when {lit}`t` has these
three columns. Proof sketch: {name}`Resolved.Query.Simple.results_eq`; a row maps to the list of its own cells. -/
theorem Resolved.Query.results_copy {query : Resolved.Query} (simple : query.Simple) (context : Resolved.EvalContext)
    (width : Nat) (noFilter : query.filter = none)
    (copies : query.columns = (List.range width).map fun position => .scalar (.column position))
    (rows : List (List Value)) (wide : ∀ row ∈ rows, row.length = width) : query.results context rows = rows := by
  rw [simple.results_eq, copies]
  have unfiltered : Resolved.filtered context query rows = rows := by
    simp [Resolved.filtered, noFilter]
  rw [unfiltered]
  conv => rhs; rw [← List.map_id rows]
  apply List.map_congr_left
  intro row member
  simp only [List.map_map, id]
  have same : (List.range width).map (fun position => row.getD position .null) = row := by
    apply List.ext_getElem?
    intro position
    have length := wide row member
    by_cases inside : position < width
    · have cell := getElem?_eq_some_getD row position (by omega)
      simp only [List.getElem?_map, List.getElem?_range inside, Option.map_some]
      exact cell.symm
    · have outside : row.length ≤ position := by omega
      simp [inside, List.getElem?_eq_none outside]
  exact same

/-- For every rows that have as many cells as the target columns and that are stored in the form of the
columns ({name}`Row.Stored`): the full rows of an INSERT from a query whose cells are the result columns in
order ({name}`insertSelectRows`) are the rows. In plain words, an INSERT that selects every column in order
changes no cell when the cells are already in the stored form of the target. Proof sketch: each cell is
{name}`Value.store` of the result cell with the affinity of its column, which is the cell. -/
theorem insertSelectRows_copy (context : Resolved.EvalContext) (columns : List CatalogColumn) (rows : List (List Value))
    (wide : ∀ row ∈ rows, row.length = columns.length)
    (stored : ∀ row ∈ rows, (⟨0, row⟩ : Row).Stored columns) :
    insertSelectRows context columns ((List.range columns.length).map Resolved.SourceCell.source) rows = rows := by
  unfold insertSelectRows
  conv => rhs; rw [← List.map_id rows]
  apply List.map_congr_left
  intro row member
  apply List.ext_getElem?
  intro position
  have length := wide row member
  by_cases inside : position < columns.length
  · have atRow := getElem?_eq_some_getD row position (by omega)
    have atColumn : columns[position]? = some columns[position] := List.getElem?_eq_getElem inside
    have fixed := stored row member position columns[position] _ atColumn atRow
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_range inside, Option.map_some,
      Nat.zero_add, atColumn, Resolved.SourceCell.valueOver]
    simp only [Option.getD_some, id_eq, fixed]
    exact atRow.symm
  · have outside : row.length ≤ position := by omega
    simp [inside, List.getElem?_eq_none outside]

end Belay.Sqlite.Model
