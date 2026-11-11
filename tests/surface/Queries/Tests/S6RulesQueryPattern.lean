import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: the guide's migration query pattern proved with the
general dependency-certificate rules (ADR 0017, S6). The migration adds a lowercase copy of a name column and
backfills it. The lookup of an id by name reads only the old columns, so for every bound value the lookup before
the migration and after it give the same values and outputs (preservation), and with the clock held constant the
lookup commutes fully with the migration. The package holds only the general rules; the table, the statements,
the certificate and the cells appended by the backfill are part of this fixture. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesQueryPattern
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- One item before the lowercase column exists. -/
def sample : Database := db! r"
  CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT NOT NULL, qty INTEGER);
  INSERT INTO items VALUES(1, 'Ada', 5);"

/-- A complete environment with a constant clock and the counters after the setup insert. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The lookup of the ids of the items with a given name. -/
def lookup (name : Value) : Script := sql r"SELECT id FROM items WHERE name = ?1" name

/-- The migration: add the lowercase column and backfill it. -/
def expansion : Script := sql r"
  ALTER TABLE items ADD COLUMN name_lower TEXT;
  UPDATE items SET name_lower = lower(name);"

/-- The original context: the sample database, the environment and no outputs. -/
def initial : ExecutionContext := ExecutionContext.initial sample environment

/-- The connection that the model's run of the migration reaches from the original context. -/
def reachedConnection : Connection :=
  (runScriptFrom runContext initial.clock initial.index initial.connection expansion.statements).connection

/-- The one statement of the lookup, which does not depend on the bound value. -/
def lookupStatement : Syntax.Statement := ((lookup .null).statements.head (by decide +kernel)).1

/-- The lookup script sends its statement with the bound value. Proof sketch: by definition. -/
theorem lookup_statements (name : Value) : (lookup name).statements = [(lookupStatement, [name])] := by rfl

/-- The resolved lookup: a simple read of the table at position 0 that keeps the rows whose column 1 equals
parameter 1 and returns column 0. -/
def lookupResolved : Resolved.Statement :=
  .query (Resolved.Query.simple [Resolved.QuerySource.first 0]
    (some (.compare .eq (some .text) (.column 1) (.parameter 1) .binary)) [.scalar (.column 0)] ["id"]) []

/-- Whether a statement resolves at a state of resolution to the expected resolved statement. -/
def resolvesTo (state : ResolveState) (statement : Syntax.Statement) (expected : Resolved.Statement) : Bool :=
  match resolveStatement runContext state statement with
  | .ok (resolved, _) => decide (resolved = expected)
  | .error _ => false

/-- If the check succeeds, the statement resolves to the expected statement. Proof sketch: invert the match. -/
theorem resolvesTo_sound {state : ResolveState} {statement : Syntax.Statement} {expected : Resolved.Statement}
    (checked : resolvesTo state statement expected = true) :
    ∃ after, resolveStatement runContext state statement = .ok (expected, after) := by
  unfold resolvesTo at checked
  split at checked
  · rename_i resolved after same
    simp at checked
    exact ⟨after, by rw [same, checked]⟩
  · cases checked

/-- The lookup resolves to the simple read on the original connection. Proof sketch: kernel evaluation. -/
theorem resolves_original : resolvesTo initial.connection.resolveState lookupStatement lookupResolved = true := by
  decide +kernel

/-- The lookup resolves to the same simple read on the connection after the migration: its column
list is fixed by the resolved statement, not by the new column. Proof sketch: kernel evaluation. -/
theorem resolves_reached : resolvesTo reachedConnection.resolveState lookupStatement lookupResolved = true := by
  decide +kernel

/-- The certificate that the untrusted analysis gives for the resolved lookup at the width 3 of the original
table. -/
def certificate : ReadCertificate :=
  match ReadAnalysis.analyze 3 lookupResolved with
  | .certified found => found
  | .unknown _ => ⟨0, 0, none, []⟩

/-- The analysis certifies the lookup. Proof sketch: kernel evaluation of the analysis. -/
theorem analysis : ReadAnalysis.analyze 3 lookupResolved = .certified certificate := by decide +kernel

/-- The certificate is valid. Proof sketch: {name}`ReadAnalysis.analyze_sound`. -/
theorem certificate_valid : certificate.Valid := (ReadAnalysis.analyze_sound analysis).1

/-- The obligations of the certificate hold between the original connection and the connection after the
migration, for the lookup statement. The backfill appends the lowercase of the name cell to each row.
Proof sketch: the two resolutions are the checks above; the scans are compared by kernel evaluation, with
the lowercase cell as the appended cells. -/
theorem obligations : certificate.Obligations runContext lookupStatement initial.connection reachedConnection := by
  refine ⟨ReadAnalysis.resolvesOriginal (resolvesTo_sound resolves_original).choose_spec analysis, ?_⟩
  obtain ⟨after, found⟩ := resolvesTo_sound resolves_reached
  refine ⟨name! "items", 0, _, _, fun row => [Resolved.mapText Resolved.lowerByte (row.getD 1 .null)], rfl, rfl,
    ⟨["id"], after, by rw [found]; rfl⟩, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-- No statement of the migration is written as INSERT from a query, so each has one execution. Proof sketch:
kernel evaluation of the syntax of the four statements. -/
theorem expansion_single : ∀ entry ∈ expansion.statements, entry.1.isInsertSelect = false := by
  decide +kernel

/-- For every bound value, the lookup before the migration and after it give the same values and outputs, on
the actual run and on every branch: the migration preserves the lookup at the original context. Proof sketch:
{name}`ReadCertificate.preservesAt_send` with the obligations. -/
theorem lookup_preserved (name : Value) :
    Migration.PreservesAt (send expansion) (fun _ => True) (send (lookup name)) initial := by
  have := ReadCertificate.preservesAt_send expansion certificate_valid lookupStatement [name] (fun _ => True)
    initial expansion_single (fun _ => obligations)
  unfold send
  rw [lookup_statements]
  exact this

/-- The contexts of the full commutation claim: the original connection and clock, at any statement index and
after any outputs. The clock gives one date at every index, as the claim needs. -/
def admitted (state : ExecutionContext) : Prop :=
  state.connection = initial.connection ∧ state.clock = initial.clock

/-- For every bound value, the lookup commutes fully with the migration at every admitted context where the
migration succeeds: the lookup first and then the migration, or the migration first and then the lookup, return
the same values and outputs, reach the same connection, counters included, and take the same number of
statements. Proof sketch: {name}`ReadCertificate.commutesOn_send` with the obligations at the connection that the
script reaches; the clock is constant, and the admitted contexts stay admitted after the lookup. -/
theorem lookup_commutes (name : Value) :
    Migration.CommutesOn (send expansion) admitted (send (lookup name)) := by
  have := ReadCertificate.commutesOn_send expansion certificate_valid lookupStatement [name] admitted expansion_single
    (fun state same assignment member one other => by
      rw [same.2] at member
      cases member
      rfl)
    (fun state domain => by
      obtain ⟨⟨connection, clock⟩, -⟩ := domain
      rw [connection, clock]
      exact obligations)
    (fun state domain selected => domain.1)
  unfold send
  rw [lookup_statements]
  exact this

#print axioms resolvesTo_sound
#print axioms resolves_original
#print axioms resolves_reached
#print axioms analysis
#print axioms certificate_valid
#print axioms obligations
#print axioms lookup_preserved
#print axioms lookup_commutes

end S6RulesQueryPattern
