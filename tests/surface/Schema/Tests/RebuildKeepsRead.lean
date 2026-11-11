import RebuildKeepsFinish

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The read of the sessions has a certificate that survives the rebuild (ADR 0017, S6, part 3). The rebuild moves
the sessions from position 1 to position 0 and appends nothing to their rows, so the obligations of the certificate
hold between the connection where a branch starts and the connection where it ends, whichever rows the database has.
The facts about the end of a branch come from {lit}`RebuildKeepsInvariant`. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- The one statement of {name}`allSessions`. -/
def sessionsRead : Syntax.Statement := (allSessions.statements.head (by decide +kernel)).1

/-- The resolved read when the sessions are at the given position: all three columns of all rows. -/
def sessionsResolvedAt (position : Nat) : Resolved.Statement :=
  .query (Resolved.Query.simple [Resolved.QuerySource.first position] none
    [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2)] ["id", "customer_id", "expires_at"]) []

/-- The certificate that the untrusted analysis gives for the read at the width 3 of the sessions. -/
def sessionsCertificate : ReadCertificate :=
  match ReadAnalysis.analyze 3 (sessionsResolvedAt 1) with
  | .certified found => found
  | .unknown _ => ⟨0, 0, none, []⟩

/-- The analysis certifies the read. Proof sketch: kernel evaluation of the analysis. -/
theorem sessions_analysis : ReadAnalysis.analyze 3 (sessionsResolvedAt 1) = .certified sessionsCertificate := by
  decide +kernel

/-- The certificate is valid. Proof sketch: {name}`ReadAnalysis.analyze_sound`. -/
theorem sessionsCertificate_valid : sessionsCertificate.Valid := (ReadAnalysis.analyze_sound sessions_analysis).1

/-- The certificate is for the position 1 and the width 3 of the sessions. Proof sketch: kernel evaluation. -/
theorem sessionsCertificate_place : sessionsCertificate.position = 1 ∧ sessionsCertificate.width = 3 := by
  decide +kernel

/-- The moved certificate describes the read at position 0. Proof sketch: kernel evaluation. -/
theorem sessions_moved : (sessionsCertificate.moved 0).statement ["id", "customer_id", "expires_at"] =
    sessionsResolvedAt 0 := by decide +kernel

/-- The read resolves to the read of position 1 where the connection has the catalog of the sample and is idle.
Proof sketch: kernel evaluation. -/
theorem sessions_resolves_before : ∃ state, resolveStatement runContext sample.raw.connection.resolveState
    sessionsRead = .ok (sessionsResolvedAt 1, state) := by
  have checked : (match resolveStatement runContext sample.raw.connection.resolveState sessionsRead with
      | .ok (resolved, _) => decide (resolved = sessionsResolvedAt 1)
      | .error _ => false) = true := by decide +kernel
  split at checked
  · rename_i resolved state same
    simp only [decide_eq_true_eq] at checked
    exact ⟨state, by rw [same, checked]⟩
  · cases checked

/-- The read resolves to the read of position 0 where the connection is the one that the whole rebuild reaches on
the sample. Proof sketch: kernel evaluation. -/
theorem sessions_resolves_after : ∃ state, resolveStatement runContext (reachedAfter 9).resolveState
    sessionsRead = .ok (sessionsResolvedAt 0, state) := by
  have checked : (match resolveStatement runContext (reachedAfter 9).resolveState sessionsRead with
      | .ok (resolved, _) => decide (resolved = sessionsResolvedAt 0)
      | .error _ => false) = true := by decide +kernel
  split at checked
  · rename_i resolved state same
    simp only [decide_eq_true_eq] at checked
    exact ⟨state, by rw [same, checked]⟩
  · cases checked

end RebuildGuide
