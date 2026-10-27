import Belay.Sqlite.Model.ForeignKeyStatementCheck
import Belay.Sqlite.Model.ReadOnlyFrame

set_option doc.verso true

/-! The database-wide {lit}`PRAGMA foreign_key_check` as a step that continues (ADR 0017, S6). The rows of the
pragma can be empty or not: a script that runs the pragma before it commits goes on in both cases. The
step is a read-only query, so it changes nothing. -/

namespace Belay.Sqlite.Model

/-- For every list without repeats and every function that gives nothing at the positions other than one: the
function gives at most one item over the list. Proof sketch: induction on the list; the first position gives the
only item or nothing, and the rest of the list does not repeat the position. -/
theorem filterMap_length_le_one (only : Nat) (items : Nat → Option (List (List Value))) :
    ∀ positions : List Nat, positions.Nodup → (∀ position ∈ positions, position ≠ only → items position = none) →
      (positions.filterMap items).length ≤ 1
  | [], _, _ => by simp
  | position :: rest, nodup, quiet => by
    by_cases same : position = only
    · subst same
      have none : rest.filterMap items = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro other member
        exact quiet other (List.mem_cons_of_mem _ member) (fun equal => (List.nodup_cons.mp nodup).1 (equal ▸ member))
      cases found : items position <;> simp [List.filterMap_cons, found, none]
    · rw [List.filterMap_cons, quiet position (List.mem_cons_self ..) same]
      exact filterMap_length_le_one only items rest (List.nodup_cons.mp nodup).2
        (fun other member => quiet other (List.mem_cons_of_mem _ member))

/-- For every database in which every table other than the one at a position gives no row of
{lit}`PRAGMA foreign_key_check` ({name}`Database.keyCheckRows`), whatever the rows of the other tables are, the
pragma of every table gives rows: the model generates them. In plain words, if at most one table has a foreign
key, the model can answer the foreign-key check of the database. Proof sketch: the tables that give rows are
among the one at the position, so the model does not meet the case of two tables
({name}`Database.foreignKeyCheckRows`). -/
theorem Database.foreignKeyCheckRows_isSome (database : Database) (only : Nat)
    (quiet : ∀ position table, position ≠ only → database.table position = some table →
      database.keyCheckRows position table = []) :
    ∃ rows, (Resolved.PragmaRows.foreignKeyCheck none).rowsOn database = some rows := by
  show ∃ rows, database.foreignKeyCheckRows none = some rows
  unfold Database.foreignKeyCheckRows
  cases blocks : database.blocks (database.checkPositions none) database.keyCheckRows with
  | nil => exact ⟨[], rfl⟩
  | cons rows rest =>
    cases rest with
    | nil => exact ⟨rows, rfl⟩
    | cons _ _ =>
      exfalso
      have short : (database.blocks (database.checkPositions none) database.keyCheckRows).length ≤ 1 := by
        unfold Database.blocks
        refine filterMap_length_le_one only _ _ (by simpa [Database.checkPositions] using List.nodup_range) ?_
        intro position _ other
        cases present : database.table position with
        | none => rfl
        | some table => simp only [Option.bind_some, quiet position table other present]
      rw [blocks] at short
      simp at short

/-- For every connection, values and table choice, if the pragma gives rows
({lit}`rowsOn` is {lit}`some`, so exactly one table gives rows or none does), the output of the resolved
pragma is no error and no stop of the model. In plain words, a foreign-key check whose rows the model
generates has rows or none, and never fails. Proof sketch: without rows the output is the empty result
({name}`resolvedStepOutput_keyCheck_empty`); with rows it has rows
({name}`resolvedStepOutput_simple_hasRows`), which are neither an error nor a stop. -/
theorem resolvedStepOutput_keyCheck_rows (index : Nat) (connection : Connection) (parameters : List Value)
    (table : Option Nat) (rows : List (List Value))
    (found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some rows) :
    (resolvedStepOutput none index connection parameters (keyCheckQuery table)).isError = false ∧
      ∀ reason, resolvedStepOutput none index connection parameters (keyCheckQuery table) ≠ .unmodeled reason := by
  by_cases empty : rows = []
  · subst empty
    rw [(resolvedStepOutput_keyCheck_empty index connection parameters table).mpr found]
    exact ⟨rfl, fun _ => nofun⟩
  · let query := pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames
    have source := keyCheckQuery_source (connection.queryContext parameters query []) connection.state.database table
      rows found
    obtain ⟨row, inRows⟩ := List.exists_mem_of_ne_nil rows empty
    have hasRows := (resolvedStepOutput_simple_hasRows index connection parameters query (keyCheckQuery_simple table)
      { rows, width := 4, fault := .none } (keyCheckQuery_calm table) source rfl).mpr
      ⟨row, inRows, by simp [query, pragmaQuery]⟩
    exact ⟨Output.hasRows_not_isError _ hasRows, fun reason same => by
      rw [show resolvedStepOutput none index connection parameters (keyCheckQuery table) =
        resolvedStepOutput none index connection parameters (.query query []) from rfl] at same
      rw [same] at hasRows
      simp [Output.hasRows] at hasRows⟩

/-- For every context, clock, index, connection and values, if no catalog position has a foreign-key mismatch
and the pragma gives rows ({lit}`rowsOn` is {lit}`some`), the step of the database-wide
{lit}`PRAGMA foreign_key_check` continues with an output that is no error, without further executions, and the
next connection is the connection. In plain words, the check goes on, whether it finds violations or not, and
changes nothing. Proof sketch: the output of the step is that of the resolved pragma
({name}`runScriptStep_output`, {name}`resolvedStepOutput_keyCheck_clock`), which is no stop of the model
({name}`resolvedStepOutput_keyCheck_rows`), so the step continues; {name}`runScriptStep_readOnly_keeps` gives
the rest. -/
theorem runScriptStep_keyCheck_continues (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (parameters : List Value) (rows : List (List Value))
    (prepares : ∀ position < connection.state.database.catalog.length,
      connection.state.database.catalog.keyMismatch position = none)
    (found : (Resolved.PragmaRows.foreignKeyCheck none).rowsOn connection.state.database = some rows) :
    ∃ output, runScriptStep context clock index connection (.pragma (.foreignKeyCheck none)) parameters =
      .continued output connection [] ∧ output.isError = false := by
  have prepared := (resolvePragma_keyCheck_iff connection.resolveState).mpr prepares
  have resolved : resolveStatement context connection.resolveState (.pragma (.foreignKeyCheck none)) =
      .ok (keyCheckQuery none, connection.resolveState) := by
    simp only [statement_arms, resolveStatementPragma_foreignKeyCheck, prepared]
  have out := runScriptStep_output context clock index connection (.pragma (.foreignKeyCheck none)) parameters
  rw [resolved] at out
  simp only [] at out
  rw [resolvedStepOutput_keyCheck_clock] at out
  obtain ⟨noError, modeled⟩ := resolvedStepOutput_keyCheck_rows index connection parameters none rows found
  cases step : runScriptStep context clock index connection (.pragma (.foreignKeyCheck none)) parameters with
  | ended reason =>
    rw [step] at out
    exact absurd out.symm (modeled reason)
  | continued output next others =>
    rw [step] at out
    obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps resolved (Or.inl ⟨_, _, rfl⟩) step
    exact ⟨output, rfl, by rw [show output = _ from out]; exact noError⟩

end Belay.Sqlite.Model
