import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: statements that the dependency-certificate rules must
not certify, and a certificate that is not valid (ADR 0017, S6). A write has a count of changes that differs after
a migration. A statement that the model refuses to resolve ends the run and has no certificate. A certificate with
a width that is too small is not valid. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesNegativeCertificates
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- One item before the migration. -/
def sample : Database := db! r"
  CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT NOT NULL, qty INTEGER);
  INSERT INTO items VALUES(1, 'Ada', 5);"

/-- A complete environment with a constant clock and the counters after the setup insert. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The migration: add a column and backfill it. The backfill changes one row. -/
def expansion : Script := sql r"
  ALTER TABLE items ADD COLUMN name_lower TEXT;
  UPDATE items SET name_lower = lower(name);"

/-- The original context. -/
def initial : ExecutionContext := ExecutionContext.initial sample environment

/-- The connection that the model's run of the migration reaches. -/
def reachedConnection : Connection :=
  (runScriptFrom runContext initial.clock initial.index initial.connection expansion.statements).connection

/-- The first statement of a script. The scripts of this fixture have one statement each. -/
def firstStatement (script : Script) (nonempty : script.statements ≠ [] := by decide +kernel) : Syntax.Statement :=
  (script.statements.head nonempty).1

/-- Whether a statement resolves at a state of resolution to a statement that the analysis does not certify at
the width. -/
def analysisUnknown (width : Nat) (state : ResolveState) (statement : Syntax.Statement) : Bool :=
  match resolveStatement runContext state statement with
  | .ok (resolved, _) => match ReadAnalysis.analyze width resolved with
    | .unknown _ => true
    | .certified _ => false
  | .error _ => false

-- A different count of changes

/-- A write whose output is the number of rows that it changes. -/
def zeroQuantity : Syntax.Statement := firstStatement (sql r"UPDATE items SET qty = 0")

/-- The migration that adds a second row. -/
def addRow : Script := sql r"INSERT INTO items VALUES(2, 'Bob', 7)"

/-- The connection after the added row. -/
def rowAdded : Connection :=
  (runScriptFrom runContext initial.clock initial.index initial.connection addRow.statements).connection

/-- The analysis gives no certificate for a write. Proof sketch: kernel evaluation. -/
theorem write_unknown : analysisUnknown 3 initial.connection.resolveState zeroQuantity = true := by
  decide +kernel

/-- The write reports one change before the added row and two after it. A frame on tables could not hide
that. Proof sketch: kernel evaluation of the two steps. -/
theorem change_counts_differ :
    (runScriptStep runContext initial.clock 0 initial.connection zeroQuantity []).output = .done 1 ∧
    (runScriptStep runContext initial.clock 1 rowAdded zeroQuantity []).output = .done 2 := by decide +kernel

-- Unmodeled syntax

/-- A read of SQLite's own table, which the model refuses to resolve. -/
def schemaRead : Syntax.Statement := firstStatement (sql r"SELECT name FROM sqlite_schema")

/-- The model ends the run at the schema read; it is not an empty effect. Proof sketch: kernel
evaluation of the step. -/
theorem schema_read_ends_run :
    ∃ reason, runScriptStep runContext initial.clock 0 initial.connection schemaRead [] = .ended reason := by
  cases step : runScriptStep runContext initial.clock 0 initial.connection schemaRead [] with
  | ended reason => exact ⟨reason, rfl⟩
  | continued output next others =>
    exfalso
    have ended : (match runScriptStep runContext initial.clock 0 initial.connection schemaRead [] with
        | .ended _ => true | .continued _ _ _ => false) = true := by decide +kernel
    rw [step] at ended
    cases ended

/-- No certificate has the obligations for the schema read: the statement does not resolve. Proof sketch: the
first obligation names a resolution, which the model refuses. -/
theorem schema_read_no_certificate (certificate : ReadCertificate) :
    ¬ certificate.Obligations runContext schemaRead initial.connection reachedConnection := by
  intro obligations
  obtain ⟨names, state, resolved⟩ := obligations.resolvesOriginal
  have refused : (match resolveStatement runContext initial.connection.resolveState schemaRead with
      | .error _ => true | .ok _ => false) = true := by decide +kernel
  rw [resolved] at refused
  cases refused

-- An invalid certificate

/-- The resolved lookup of the ids of the items with a given name. -/
def lookupResolved : Resolved.Statement :=
  .query (Resolved.Query.simple [Resolved.QuerySource.first 0]
    (some (.compare .eq (some .text) (.column 1) (.parameter 1) .binary)) [.scalar (.column 0)] ["id"]) []

/-- A certificate for the lookup with width 1. The lookup reads column 1 in its filter, so the width is a
false claim. -/
def narrow : ReadCertificate :=
  ⟨0, 1, some (.compare .eq (some .text) (.column 1) (.parameter 1) .binary), [.scalar (.column 0)]⟩

/-- The narrow certificate is not valid: its soundness obligation, that the filter reads only columns below the
width, fails for column 1. Proof sketch: the filter reads column 1, which is not below 1; kernel evaluation. -/
theorem narrow_invalid : ¬ narrow.Valid := by
  intro valid
  have := valid.filterBelow _ rfl
  revert this
  decide +kernel

/-- The analysis refuses the width 1 for the lookup. Proof sketch: kernel evaluation. -/
theorem narrow_refused : ReadAnalysis.analyze 1 lookupResolved = .unknown .readsBeyondWidth := by
  decide +kernel

#print axioms write_unknown
#print axioms change_counts_differ
#print axioms schema_read_ends_run
#print axioms schema_read_no_certificate
#print axioms narrow_invalid
#print axioms narrow_refused

end S6RulesNegativeCertificates
