import RebuildKeepsRead

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! Claim 1 of the guide's table rebuild (ADR 0017, S6, part 3): the rebuild {lit}`requireName` preserves the read
{lit}`allSessions` of the sessions on every database whose catalog is the guide's schema. The rebuild is an INSERT
from a query, so its branches can reach different connections. The facts that each step keeps
({lit}`RebuildKeepsInvariant`, {lit}`RebuildKeepsFinish`) hold at the end of every branch
({lit}`sendStatements_branch_invariant`), and with them the obligations of the certificate of
{lit}`RebuildKeepsRead` hold between the start and the end of each branch. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For every database of the guide's schema: the name of the sessions finds a table at position 1. Proof sketch: the
sample finds the name at position 1, and the lookup depends on the catalog only. -/
theorem sessions_found {db : Database} (pre : db.raw.catalog = sample.raw.catalog) :
    ∃ sessions, db.raw.tableNamed sessionsName = some (1, sessions) := by
  have atOne : (sample.raw.catalog.findTable sessionsName).map (·.1) = some 1 := by decide +kernel
  cases lookup : db.raw.catalog.findTable sessionsName with
  | none => rw [← pre, lookup] at atOne; simp at atOne
  | some found =>
    obtain ⟨place, shape⟩ := found
    rw [← pre, lookup] at atOne
    simp only [Option.map_some, Option.some.injEq] at atOne
    subst atOne
    exact ⟨_, by rw [Database.tableNamed_of_findTable lookup, Database.table_of_findTable _ _ _ _ lookup]; rfl⟩

/-- For every database of the guide's schema: every row of the sessions has at least the 3 cells of the width of the
certificate. Proof sketch: a valid database stores rows with one cell for each column
({lit}`Database.RowsWide`), and the sample has 3 columns in the sessions. -/
theorem sessions_wide {db : Database} (pre : db.raw.catalog = sample.raw.catalog) {sessions : Table}
    (named : db.raw.tableNamed sessionsName = some (1, sessions)) :
    ∀ row ∈ Resolved.sourceRows sessions, sessionsCertificate.width ≤ row.length := by
  obtain ⟨lookup, present⟩ := Database.tableNamed_some named
  have columns : (sample.raw.catalog.findTable sessionsName).map (·.2.columns.length) = some 3 := by
    decide +kernel
  rw [← pre, lookup] at columns
  simp only [Option.map_some, Option.some.injEq] at columns
  intro row member
  obtain ⟨stored, inScan, rfl⟩ := List.mem_map.mp member
  have wide := db.valid.admitted.rowsWide 1 sessions present stored
    ((sessions.scanRows_perm.mem_iff).mp inScan)
  rw [sessionsCertificate_place.2, ← columns]
  exact Nat.le_of_eq wide.symm

/-- For every database of the guide's schema, table of the sessions in it and connection that keeps the facts of the
rebuild after all its statements: the obligations of the certificate hold between the connection to the database and
that connection. Proof sketch: the resolution state of the end is the one that the sample reaches, so the read
resolves at position 0 there; the table is the same, with the same rows. -/
theorem sessions_obligations {db : Database} {counters : Counters} {ended : Connection} {sessions : Table}
    (pre : db.raw.catalog = sample.raw.catalog) (named : db.raw.tableNamed sessionsName = some (1, sessions))
    (kept : Kept sessions 9 ended) :
    sessionsCertificate.Obligations runContext sessionsRead (db.raw.connection counters) ended := by
  obtain ⟨before, resolvedBefore⟩ := sessions_resolves_before
  obtain ⟨after, resolvedAfter⟩ := sessions_resolves_after
  have sameState : (db.raw.connection counters).resolveState = sample.raw.connection.resolveState := by
    simp [Database.Raw.connection, Connection.resolveState, pre]
  refine ⟨?_, ?_⟩
  · exact ReadAnalysis.resolvesOriginal (by rw [sameState]; exact resolvedBefore) sessions_analysis
  · refine ⟨sessionsName, 0, sessions, sessions, fun _ => [], ?_, ?_,
      ⟨["id", "customer_id", "expires_at"], after, ?_⟩, by simp, sessions_wide pre named⟩
    · rw [sessionsCertificate_place.1]; exact named
    · simpa [sessionsPosition] using kept.2
    · rw [kept.1, sessions_moved]; exact resolvedAfter

/-- For every clock and table of the sessions, every statement of the rebuild, and every connection that keeps the
facts before the statement: every execution of the step of the statement that has no error output reaches a connection
that keeps the facts after the statement. Proof sketch: the nine cases {lit}`advance_0` to {lit}`advance_8`. -/
theorem kept_advance (clock : Option Clock) (sessions : Table) :
    ∀ (n : Nat) (inList : n < requireName.statements.length) (index : Nat) (connection : Connection),
      connection.state.Holds (Database.Valid Profile.pinned) → Kept sessions n connection →
      ∀ output next others, runScriptStep runContext clock index connection requireName.statements[n].1
          requireName.statements[n].2 = .continued output next others →
        ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
          Kept sessions (n + 1) found.next := by
  intro n inList index connection _ kept output next others step
  have small : n < 9 := inList
  match n, small with
  | 0, _ => exact advance_0 kept step
  | 1, _ => exact advance_1 kept step
  | 2, _ => exact advance_2 kept step
  | 3, _ => exact advance_3 kept step
  | 4, _ => exact advance_4 kept step
  | 5, _ => exact advance_5 kept step
  | 6, _ => exact advance_6 kept step
  | 7, _ => exact advance_7 kept step
  | 8, _ => exact advance_8 kept step

/-- The rebuild preserves the read of all sessions on every database whose catalog is the guide's schema, for every
complete environment: where the rebuild succeeds on the database, the read before the rebuild and the read after it
give the same value and the same outputs, on the actual run and on every branch. The databases are unrestricted
otherwise: the customers and sessions can have any rows. Where the rebuild fails on a database, the claim requires
nothing. Proof sketch: {name}`ReadCertificate.preservesAt` with the certificate of the read; the obligations come
from {name}`sendStatements_branch_invariant`, with the facts that each step keeps, and from
{name}`sessions_obligations`. -/
theorem requireName_preserves_allSessions :
    Migration.QueryPreserves (send requireName) allSessions (fun db => db.raw.catalog = sample.raw.catalog) := by
  intro db pre env complete
  obtain ⟨sessions, named⟩ := sessions_found pre
  have start : Kept sessions 0 (db.raw.connection env.counters) := by
    have sameDatabase : (db.raw.connection env.counters).state.database = db.raw := rfl
    refine ⟨?_, by rw [sameDatabase]; simpa [sessionsPosition] using named⟩
    have same : (db.raw.connection env.counters).resolveState = sample.raw.connection.resolveState := by
      simp [Database.Raw.connection, Connection.resolveState, pre]
    rw [same]
    with_unfolding_all rfl
  exact ReadCertificate.preservesAt (send requireName) sessionsCertificate_valid sessionsRead [] (fun _ => True)
    (ExecutionContext.initial db env) fun domain branch ran => by
      have ok := (Sql.succeedsFrom_iff_branches _ _ _ _).mp domain.2 branch ran
      exact sessions_obligations pre named (sendStatements_branch_invariant requireName.statements (Kept sessions)
        env.clock 0 (db.raw.connection env.counters) branch ran ok.1 ok.2
        ⟨db.valid, fun _ shown => by simp [Database.Raw.connection] at shown⟩ start (kept_advance env.clock sessions))

#print axioms requireName_preserves_allSessions

end RebuildGuide
