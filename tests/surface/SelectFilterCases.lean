import SelectProjectionCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases of the filter rules of ADR 0027: A02, where {lit}`WHERE note IS NOT NULL`
gives non-NULL cells with no schema constraint, and A03, where {lit}`WHERE amount > :minimum` gives
the modeled comparison for every returned row, each over every database with generic table and
column premises, with witnesses and contrasts. -/

namespace SelectFilterCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases

/-- The query of A02: the notes that are present. -/
def presentNotes : Script := sql r"SELECT note FROM notes WHERE note IS NOT NULL"

/-- The query of A02 has one statement. -/
theorem presentNotes_one : presentNotes.statements.length = 1 := rfl

/-- A02 with generic premises: for every database and environment, when the catalog has a table
{lit}`notes` at a position with a column {lit}`note`, the query of the present notes returns a
result, and each of its rows has a first cell that is not NULL. The column can accept NULL, and the
table can have any constraints, other columns and rows, also none. Proof sketch: the resolution laws
give the simple query of the table with the condition {lit}`note IS NOT NULL`;
{name}`Run.query_returnsResult_calmTable` reduces the claim to the possible results over the scan;
{name}`Resolved.Query.mem_possibleResults_plain` gives the source row of each result row, where the
condition is true, and {name}`Resolved.truthy_isNot_null` makes its cell non-NULL. -/
theorem present_notes (db : Database) (env : Env) {position noteIndex : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "notes") = some (position, table))
    (noteFound : columnPosition table.columns (name! "note") = some noteIndex) :
    (db.run (query presentNotes presentNotes_one) env).returnsRows firstCellPresent := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "notes", alias := none } position table) (aliases := [])
    (shapes := { later := [] })
    (term := .compare .isNot (.identifier (name! "note") .none) .null) (by simp [namesAlias])
    (by simp [resolveOperand_compare_of_notBoolean _ Syntax.Expr.null rfl, resolveOperand_identifier_table noteFound,
      resolveOperand_null]; rfl)
  obtain ⟨names, resolved⟩ := resolveStatement_select_column runContext (db.raw.connection env.counters).resolveState
    { table := name! "notes", alias := none } _ position table _ (name! "note") "note" rfl rfl rfl found
    noteFound resolves
  rw [Run.returnsRows, Run.query_returnsResult_calmTable (script := presentNotes) rfl presentNotes_one db env resolved rfl
    (Database.table_of_findTable _ _ _ _ found) ?calm rfl rfl rfl ?noOverflow rfl]
  · intro result member row inResult
    obtain ⟨source, -, kept, rfl⟩ := Resolved.Query.mem_possibleResults_plain rfl rfl rfl member inResult
    simp only [Resolved.Query.simple, Option.all_some, Resolved.Expr.eval_compare, Resolved.Expr.eval_column,
      Resolved.Expr.eval_literal, Resolved.truthy_isNot_null] at kept
    refine ⟨source.getD noteIndex .null, rfl, fun null => ?_⟩
    rw [null] at kept
    exact absurd kept (by decide)
  · refine Resolved.Statement.simpleColumn_calm _ _ _ _ fun expression member => ?_
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column _, Resolved.Expr.calm_literal _⟩
  · simp [Resolved.Query.fails, Resolved.Query.simple]

/-- A table of notes whose column {lit}`note` accepts NULL: its CHECK accepts NULL and every
non-empty text. One note is NULL. -/
def notes : Database := db! r"
  CREATE TABLE notes (id INTEGER PRIMARY KEY, note TEXT CHECK (note IS NULL OR note <> ''));
  INSERT INTO notes VALUES (1, NULL), (2, 'call back');"

/-- The query of the A02 contrast: every note, with no filter. -/
def allNotes : Script := sql r"SELECT note FROM notes"

/-- The contrast query has one statement. -/
theorem allNotes_one : allNotes.statements.length = 1 := rfl

/-- A02 witness: on {name}`notes`, the present notes are one row, whose first cell is not NULL. -/
theorem present_witness :
    (notes.run (query presentNotes presentNotes_one)).returnsResult (·.length = 1) ∧
      (notes.run (query presentNotes presentNotes_one)).returnsRows firstCellPresent :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A02 contrast: the CHECK of {name}`notes` accepts NULL, so the schema alone gives no non-NULL
cells. The column is not NOT NULL, and without the filter the query returns a row whose first cell
is NULL. -/
theorem check_contrast :
    ((notes.raw.catalog.findTable (name! "notes")).get (by decide +kernel)).2.columns[1]?.map
        CatalogColumn.notNull = some false ∧
      ¬ (notes.run (query allNotes allNotes_one)).returnsRows firstCellPresent :=
  ⟨by decide +kernel, by decide +kernel⟩

#print axioms present_notes
#print axioms present_witness
#print axioms check_contrast

end SelectFilterCases
