import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeyPragmaQuery
import Belay.Sqlite.Model.Tooling.Counterexamples.OutputResultsLaws

set_option doc.verso true

/-! Foreign-key pragma row generation connected to the query statement that executes it.
Preparation remains a separate condition; empty generated rows do not establish compatible
parent schemas. -/

namespace Belay.Sqlite.Model

/-- Canonical result output collapses any nonempty list of empty alternatives to one empty result. -/
private theorem ofResults_empty (results : List (List (List Value)))
    (empty : (Output.ofResults results).hasNoRows = true) : Output.ofResults results = .rows [] := by
  obtain ⟨nonempty, each⟩ := (Output.hasNoRows_ofResults results).mp empty
  cases results with
  | nil => contradiction
  | cons first rest =>
    have firstEmpty := each first (by simp)
    subst first
    have filtered : (rest.filter fun result => !result.isEmpty) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro result member
      simp [each result (by simp [member])]
    have erased : ([] :: rest).eraseDups = [[]] := by simp [List.eraseDups_cons, filtered]
    simp [Output.ofResults, erased, Resolved.stableSort, Resolved.insertStable]

/-- For every connection, table choice, statement index and values, the prepared foreign-key
pragma returns exactly one empty row result if and only if its generated rows are empty.
An error or model restriction never satisfies either side. Proof sketch: the no-row law above,
then the canonical query output collapses empty alternatives to one empty result. -/
theorem resolvedStepOutput_keyCheck_empty (index : Nat) (connection : Connection)
    (parameters : List Value) (table : Option Nat) :
    resolvedStepOutput none index connection parameters (keyCheckQuery table) = .rows [] ↔
      (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some [] := by
  constructor
  · intro empty
    apply (resolvedStepOutput_keyCheck_hasNoRows index connection parameters table).mp
    rw [empty]
    rfl
  · intro generated
    have empty := (resolvedStepOutput_keyCheck_hasNoRows index connection parameters table).mpr generated
    let query := pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames
    change (resolvedStepOutput none index connection parameters (.query query [])).hasNoRows = true at empty
    change resolvedStepOutput none index connection parameters (.query query []) = .rows []
    have calm := keyCheckQuery_calm table
    rw [resolvedStepOutput_query index connection parameters query [] calm.readsClock (calm.firstUnknown _)] at empty ⊢
    split at empty
    · simp_all only [ite_true]
      unfold Resolved.Query.outputOn at empty ⊢
      repeat' split at empty
      all_goals simp_all only [Output.hasNoRows, Bool.false_eq_true, ite_false]
      all_goals exact ofResults_empty _ empty
    · simp [Output.hasNoRows] at empty

end Belay.Sqlite.Model
