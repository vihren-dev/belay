import Belay.Sqlite.Model.TableFailure

set_option doc.verso true

/-! The failure of an INSERT, in the order in which SQLite meets it: the rows in VALUES order, and
for each row its checks before the next row. For an INSERT with {lit}`ON CONFLICT` clauses or
algorithms, the failure of the row at which the statement stops, along the branches of
{name}`Belay.Sqlite.Model.LiteralData.upsertRow`. Theorems tie each failure to the checks of the
write, so a write that fails a constraint has a failure. -/

namespace Belay.Sqlite.Model
namespace LiteralData

/-- The rows of an INSERT that SQLite checks for constraints: those before the first row whose
rowid alias SQLite refuses ({name}`aliasMismatch`), or all rows when there is no such row. -/
def checkedPrefix (table : Table) (values : List (List Value)) : List (List Value) :=
  match values.findIdx? (aliasMismatch table.shape) with
  | some index => values.take index
  | none => values

/-- The failure of a plain INSERT of the rows: the first failure ({name}`firstFailure`) of the
table with the first rows inserted, for the fewest rows of {name}`checkedPrefix` that fail; and
when no such count fails, the first failure of the table with all checked rows inserted. -/
def insertFailure (keys : List UniqueKey) (table : Table) (values : List (List Value)) : Option TableFailure :=
  let checked := checkedPrefix table values
  ((List.range checked.length).findSome? fun count => firstFailure keys (inserted table (checked.take (count + 1)))).orElse
    fun _ => firstFailure keys (inserted table checked)

/-- For every list of keys, table and rows: if the table with the rows of {name}`checkedPrefix`
inserted fails {name}`constraints` of the keys or {name}`rowidsDistinct`, then
{name}`insertFailure` gives some failure. Proof sketch: the fallback of {name}`insertFailure` is
{name}`firstFailure` of that table ({name}`firstFailure_isSome`). -/
theorem insertFailure_isSome {keys : List UniqueKey} {table : Table} {values : List (List Value)}
    (fails : ¬(constraints keys (inserted table (checkedPrefix table values)) &&
      rowidsDistinct (inserted table (checkedPrefix table values))) = true) :
    (insertFailure keys table values).isSome := by
  unfold insertFailure
  have whole := firstFailure_isSome fails
  simp only [Option.orElse]
  split
  · rfl
  · exact whole

/-- The failure of one row of an INSERT with clauses or algorithms, along the branches of
{name}`upsertRow`:

* the row by itself ({name}`rowFailure`: NOT NULL, then {lit}`STRICT`, then CHECK);
* with a clause {lit}`DO NOTHING` that handles the row, none;
* with a clause {lit}`DO UPDATE`, the first failure of the table with the updated row;
* otherwise the keys that are not REPLACE and on which the row conflicts, when there are some;
* otherwise the first failure of the table without the rows that REPLACE deletes, with the row. -/
def upsertRowFailure (context : Resolved.EvalContext) (keys : List UniqueKey) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (table : Table) (values : List Value) : Option TableFailure :=
  let proposed := proposedRow table values
  (rowFailure table.shape proposed).orElse fun _ =>
  match handlingClause keys clauses table proposed with
  | some (clause, existing) => match clause.action with
    | .nothing => none
    | .update assignments _ =>
      let changed := movedRowid table.shape.rowidAlias
        (assignFrom context table.shape.columns assignments (existing.values ++ proposed.values) existing)
      firstFailure keys (replaceRow table existing changed)
  | none => match (List.range keys.length).filter fun index =>
        algorithmAt policy.keys index != .replace && conflictsAt keys table proposed index with
    | [] => let kept := replaced keys policy.keys table proposed
      firstFailure keys { kept with rows := kept.rows ++ [proposed] }
    | failing@(_ :: _) => some (.keys failing)

/-- For every list of keys, table, row and error: if {name}`checkedRow` fails with the error, then
{name}`firstFailure` of the table gives some failure. -/
theorem checkedRow_failure {keys : List UniqueKey} {next : Table} {written : Row} {reason : ExecutionError}
    (failed : checkedRow keys next written = .error reason) : (firstFailure keys next).isSome := by
  simp only [checkedRow] at failed
  split at failed
  · simp at failed
  · exact firstFailure_isSome (by assumption)

/-- For every row of an INSERT with clauses or algorithms and every error other than
{name}`ExecutionError.datatypeMismatch`: if {name}`upsertRow` fails with the error, then
{name}`upsertRowFailure` gives some failure. Proof sketch: follow the branches of
{name}`upsertRow`; a row that fails by itself has its {name}`rowFailure`
({name}`rowFailure_eq_none` gives the converse), a key that blocks the row is in the list of
conflicting keys, and a failed {name}`checkedRow` has a {name}`firstFailure`
({name}`checkedRow_failure`). -/
theorem upsertRowFailure_isSome {context : Resolved.EvalContext} {keys : List UniqueKey} {policy : Resolved.ConflictPolicy}
    {clauses : List Resolved.ConflictClause} {table : Table} {values : List Value} {reason : ExecutionError}
    (failed : upsertRow context keys policy clauses table values = .error reason) (typed : reason ≠ .datatypeMismatch) :
    (upsertRowFailure context keys policy clauses table values).isSome := by
  unfold upsertRowFailure
  cases single : rowFailure table.shape (proposedRow table values) with
  | some _ => simp [single]
  | none =>
    obtain ⟨nulls, types, checks⟩ := rowFailure_eq_none single
    simp only [single, Option.orElse]
    unfold upsertRow at failed
    by_cases alias : aliasMismatch table.shape values = true
    · simp only [alias, ↓reduceIte] at failed; exact absurd (by injection failed with failed; exact failed.symm) typed
    simp only [alias, nulls, types, checks, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at failed
    cases found : handlingClause keys clauses table (proposedRow table values) with
    | some pair =>
      obtain ⟨clause, existing⟩ := pair
      simp only [found] at failed ⊢
      cases action : clause.action with
      | nothing => simp [action] at failed
      | update assignments filter =>
        simp only [action, updateExisting] at failed ⊢
        split at failed
        · simp at failed
        · split at failed
          · exact absurd (by injection failed with failed; exact failed.symm) typed
          · exact checkedRow_failure failed
    | none =>
      simp only [found, insertChecked] at failed ⊢
      cases blocking : blockingKey keys policy.keys table (proposedRow table values) with
      | some index =>
        have member := List.mem_of_find?_eq_some blocking
        have holds := List.find?_some blocking
        split
        · rename_i empty
          have := List.filter_eq_nil_iff.mp empty index member
          simp_all
        · rfl
      | none =>
        simp only [blocking] at failed
        split
        · exact checkedRow_failure failed
        · rfl

/-- For every table, list of rows, error, table {lit}`reached` and written rows: if
{name}`upsertSummary` of the steps ({name}`upsertSteps`) fails with the error, then the steps
have a last step, and {name}`upsertRow` of its table and values fails with the same error. Proof
sketch: induction over the rows; the steps end at the first row that fails. -/
theorem upsertSteps_error {context : Resolved.EvalContext} {keys : List UniqueKey}
    {policy : Resolved.ConflictPolicy} {clauses : List Resolved.ConflictClause} :
    ∀ {table : Table} {rows : List (List Value)} {reason : ExecutionError} {reached : Table} {written : List Row},
    upsertSummary table (upsertSteps context keys policy clauses table rows) = .error (reason, reached, written) →
    ∃ step, (upsertSteps context keys policy clauses table rows).getLast? = some step ∧
      upsertRow context keys policy clauses step.before step.values = .error reason := by
  intro table rows
  induction rows generalizing table with
  | nil => simp [upsertSteps, upsertSummary]
  | cons values rest restError =>
    intro reason reached written summary
    simp only [upsertSteps] at summary ⊢
    cases row : upsertRow context keys policy clauses table values with
    | error error =>
      simp only [row, upsertSummary] at summary ⊢
      injection summary with summary; injection summary with summary
      exact ⟨_, rfl, by simp [row, summary]⟩
    | ok pair =>
      obtain ⟨next, out⟩ := pair
      simp only [row, upsertSummary] at summary ⊢
      split at summary
      · rename_i later laterReached laterWritten laterSummary
        injection summary with summary; injection summary with same _
        obtain ⟨step, last, stepError⟩ := restError laterSummary
        refine ⟨step, ?_, same ▸ stepError⟩
        cases steps : upsertSteps context keys policy clauses next rest with
        | nil => simp [steps] at last
        | cons _ _ => simp_all [List.getLast?_cons_cons]
      · simp at summary

end LiteralData
end Belay.Sqlite.Model
