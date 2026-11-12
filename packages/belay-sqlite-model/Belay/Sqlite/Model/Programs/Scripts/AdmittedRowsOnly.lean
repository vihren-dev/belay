import Belay.Sqlite.Model.Schema.Rows.AdmittedRowsOnly

set_option doc.verso true

/-! The plain writes that only replace the rows of one table (ADR 0022, D3, slice 4). INSERT, UPDATE,
DELETE and upsert without foreign key rules and trigger programs store the rows of the target table
({lit}`Database.setRows`), or fail and keep the database. {lit}`Database.RowsOnlyAt` says this about
a database after the statement. So the atoms of the catalog ("catalog supported" and "rows shaped")
need one proof for the four forms instead of one for each. -/

namespace Belay.Sqlite.Model

/-- For every plain statement of the four forms INSERT, UPDATE, DELETE and upsert (no rules), the
database of the effect of {name}`runStatement` on a database is {name}`Database.RowsOnlyAt` the
database at the target of the statement. Proof sketch: a missing table keeps the database; the other
cases are the lemmas {name}`insertOutcome_rowsOnly` and {name}`checkedWrite_rowsOnly`, and an upsert
stores the table of {name}`LiteralData.upsertSummary`, whether the last row succeeds or fails. -/
theorem runStatement_plain_rowsOnly (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) (database : Database) (target : Nat)
    (plain : (∃ rows returning subqueries, statement = .insert target rows returning subqueries none) ∨
      (∃ assignments filter returning subqueries,
        statement = .update target assignments filter returning subqueries none) ∨
      (∃ rows clauses returning algorithm subqueries,
        statement = .upsert target rows clauses returning algorithm subqueries none) ∨
      (∃ filter returning subqueries, statement = .delete target filter returning subqueries none)) :
    database.RowsOnlyAt target (effectDatabase (runStatement clock counters parameters statement database).effect) := by
  rcases plain with ⟨rows, returning, subqueries, rfl⟩ | ⟨assignments, filter, returning, subqueries, rfl⟩ |
    ⟨rows, clauses, returning, algorithm, subqueries, rfl⟩ | ⟨filter, returning, subqueries, rfl⟩
  · simp only [runStatement, Option.map_none, StatementRun.withKeys]
    split
    · exact .inl rfl
    · exact insertOutcome_rowsOnly ‹_› _ _ _
  · simp only [runStatement, Option.map_none, StatementRun.withKeys]
    split
    · exact .inl rfl
    · rename_i found
      split
      · exact .inl rfl
      · exact checkedWrite_rowsOnly found _ _
  · simp only [runStatement, Option.map_none, StatementRun.withKeys]
    split
    · exact .inl rfl
    · rename_i found
      dsimp only
      split <;> exact .setRows found _
  · simp only [runStatement, Option.map_none, StatementRun.withKeys]
    split
    · exact .inl rfl
    · exact .setRows ‹_› _

end Belay.Sqlite.Model
