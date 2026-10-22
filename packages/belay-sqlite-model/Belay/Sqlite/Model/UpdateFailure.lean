import Belay.Sqlite.Model.ConstraintMessages

set_option doc.verso true

/-! The constraints that SQLite may name for a plain UPDATE that fails. SQLite changes the rows one
at a time, in an order that its query planner chooses, and checks each changed row against the
table at that time (SQLite 3.51, measured with the {lit}`sqlite3` shell). The model computes the
table after the UPDATE ({name}`Belay.Sqlite.Model.LiteralData.updated`) and checks it once.

For an UPDATE of one row the two agree: the table at that time is the table after the UPDATE. For
an UPDATE of several rows, the candidates are the failures that can be the first failure of each
changed row: its NOT NULL, {lit}`STRICT` or CHECK failure, a rowid of another row, or each key on
which its new values conflict with another row in its old values or in its new values, in SQLite's
order of checks.
The argument that this list contains SQLite's choice: SQLite fails at the first changed row
{lit}`r` that fails, in the order that it visits the rows. The failures of {lit}`r` by itself do
not depend on the other rows. A rowid or a key on which {lit}`r` conflicts is that of a row
{lit}`j` of the table at that time, which is in its old values (SQLite has not changed it yet) or
in its new values. So the first failure of {lit}`r` in SQLite's order is in the list, whether
the conflicts before it happen in SQLite's order of the rows or not.
The argument does not use the form of the keys: it holds for keys with expression terms and for
partial unique indexes whose filter reads an assigned column. The list can contain constraints
that SQLite does not name in any order of the rows.

The model's effect can differ from SQLite's for such an UPDATE: SQLite can fail where the table
after the UPDATE has no conflict. Then {lit}`runStatement` succeeds and this
module is not used. -/

namespace Belay.Sqlite.Model
namespace LiteralData

/-- The positions of the keys on which the row at the position conflicts ({name}`keyEqual`) with
another row of one of the lists of rows. The lists are the rows of the table before and after an
UPDATE, which have the same positions ({name}`updated`). -/
def rowConflicts (keys : List UniqueKey) (states : List (List Row)) (position : Nat) (row : Row) : List Nat :=
  (List.range keys.length).filter fun index => (keys[index]?).any fun key =>
    states.any fun rows => rows.zipIdx.any fun (other, place) => place != position && keyEqual key other row

/-- Whether the row at the position has the rowid of another row of one of the lists of rows,
the rows of the table before and after an UPDATE. -/
def rowidConflicts (states : List (List Row)) (position : Nat) (row : Row) : Bool :=
  states.any fun rows => rows.zipIdx.any fun (other, place) => place != position && other.rowid == row.rowid

/-- The failures that can be the first failure of a changed row of the table after an UPDATE
({lit}`result`), in SQLite's order of checks: its first failure by itself before the rowid check
({name}`beforeRowidFailures` of the row alone), when it has one; otherwise a rowid that another row
of the table before the UPDATE ({lit}`before`) or after it has ({name}`rowidConflicts`), and then
its first failure after the rowid check ({name}`afterRowidFailures`), or else the keys on which it
conflicts with another row ({name}`rowConflicts`). A conflict depends on the rows that SQLite has
changed at that time, so the failures after a conflict are in the list too. The list is empty
when the row has none of these. -/
def changedRowFailures (keys : List UniqueKey) (before result : Table) (position : Nat) (row : Row) :
    List TableFailure :=
  let alone : Table := { shape := result.shape, rows := [row] }
  match (beforeRowidFailures alone).head? with
  | some failure => [failure]
  | none =>
    (if rowidConflicts [before.rows, result.rows] position row then [.rowid] else []) ++
    match (afterRowidFailures alone).head? with
    | some failure => [failure]
    | none => match rowConflicts keys [before.rows, result.rows] position row with
      | [] => []
      | failing@(_ :: _) => [.keys failing]

/-- The positions of the rows of the table that the UPDATE changes ({name}`selected`). -/
def selectedPositions (context : Resolved.EvalContext) (filter : Option Resolved.Expr) (table : Table) : List Nat :=
  (table.rows.zipIdx.filter fun (row, _) => selected context filter row).map (·.2)

end LiteralData

/-- The constraints that SQLite may name for one failure of a changed row of the table at the
position: with {lit}`exact`, those of {name}`Catalog.candidates`; without it, each failing key
of the row, because the keys that SQLite meets depend on the order of the rows. -/
def Catalog.rowCandidates (catalog : Catalog) (table : Nat) (exact : Bool) : TableFailure → List ConstraintFailure
  | .keys (first :: rest) =>
    if exact then catalog.candidates table (.keys (first :: rest)) else (first :: rest).map (.key table)
  | failure@(.keys []) | failure@(.notNull _) | failure@(.strictType _ _) | failure@(.check _) | failure@.rowid =>
    catalog.candidates table failure

/-- For every catalog, table position, flag and failure: {name}`Catalog.rowCandidates` is not
empty. Proof sketch: by cases on the failure; keys that are not empty map to a list that is not
empty, and each other case is {name}`Catalog.candidates_ne_nil`. -/
theorem Catalog.rowCandidates_ne_nil (catalog : Catalog) (table : Nat) (exact : Bool) (failure : TableFailure) :
    catalog.rowCandidates table exact failure ≠ [] := by
  cases failure with
  | keys failing =>
    cases failing with
    | nil => exact Catalog.candidates_ne_nil _ _ _
    | cons first rest => cases exact <;> simp [Catalog.rowCandidates, Catalog.candidates_ne_nil]
  | notNull _ | strictType _ _ | check _ | rowid =>
    simp only [Catalog.rowCandidates]; exact Catalog.candidates_ne_nil _ _ _

/-- The report of a plain UPDATE of the table at the position, from the positions of the changed
rows and the tables before the UPDATE ({lit}`before`) and after it ({lit}`result`): the
{name}`Catalog.rowCandidates` of the {name}`LiteralData.changedRowFailures` of each changed row,
exact when at most one row changes. With one changed row, no other row changes, so its conflicts
do not depend on an order, and the first of its failures is SQLite's. A
table whose changed rows have no failure (a table that failed before the UPDATE) gives the
candidates of each of its failures ({name}`LiteralData.tableFailures`). With several changed rows
the reason is {name}`CandidateReason.rowOrder`. -/
def Catalog.updateReport (catalog : Catalog) (table : Nat) (keys : List UniqueKey) (positions : List Nat)
    (before result : Table) : ConstraintReport :=
  let exact := positions.length ≤ 1
  let rowFailures := fun position =>
    ((result.rows[position]?).map (LiteralData.changedRowFailures keys before result position)).getD []
  let failures := match positions.flatMap fun position =>
      if exact then (rowFailures position).take 1 else rowFailures position with
    | [] => LiteralData.tableFailures keys result
    | found@(_ :: _) => found
  { candidates := failures.flatMap (catalog.rowCandidates table exact),
    reason := if exact then .primaryKeyPlace else .rowOrder }

/-- For every catalog, table position, keys, positions and tables {lit}`before` and {lit}`result`:
if the result fails {name}`LiteralData.constraints` of the keys or
{name}`LiteralData.rowidsDistinct`, then the candidates of {name}`Catalog.updateReport` are not empty. Proof sketch: the list of failures is
not empty ({name}`LiteralData.tableFailures_eq_nil_iff` for the fallback), and each failure has
candidates ({name}`Catalog.rowCandidates_ne_nil`). -/
theorem Catalog.updateReport_ne_nil {catalog : Catalog} {table : Nat} {keys : List UniqueKey} {positions : List Nat}
    {before result : Table} (fails : ¬(LiteralData.constraints keys result && LiteralData.rowidsDistinct result) = true) :
    (catalog.updateReport table keys positions before result).candidates ≠ [] := by
  simp only [Catalog.updateReport]
  split
  · rename_i none
    have nonempty : LiteralData.tableFailures keys result ≠ [] :=
      fun empty => fails ((LiteralData.tableFailures_eq_nil_iff _ _).mp empty)
    obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil nonempty
    simp only [split, List.flatMap_cons]
    exact List.append_ne_nil_of_left_ne_nil (Catalog.rowCandidates_ne_nil _ _ _ _) _
  · rename_i first rest _
    simp only [List.flatMap_cons]
    exact List.append_ne_nil_of_left_ne_nil (Catalog.rowCandidates_ne_nil _ _ _ _) _

end Belay.Sqlite.Model
