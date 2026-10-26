import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: reads that the dependency-certificate rules must not
certify (ADR 0017, S6). After a migration that appends a column, a {lit}`SELECT *` resolves to more columns, table
metadata shows the column, and a counter read sees the migration's changes. For each case the fixture proves that
the obligation of the rule fails or that the analysis answers unknown, and that the claim the rule would give is
false: the step outputs differ. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesNegativeReads
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

/-- The number of result columns of a statement that resolves to a query, and 0 for other resolutions. -/
def columnCount (state : ResolveState) (statement : Syntax.Statement) : Nat :=
  match resolveStatement runContext state statement with
  | .ok (.query query _, _) => query.columns.length
  | _ => 0

-- SELECT star after ADD COLUMN

/-- The read of every column. -/
def star : Syntax.Statement := firstStatement (sql r"SELECT * FROM items")

/-- The resolved star read: three columns. -/
def starResolved : Resolved.Statement :=
  .query (Resolved.Query.simple [Resolved.QuerySource.first 0] none
    [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2)] ["id", "name", "qty"]) []

/-- The analysis certifies the star read at the original width, because the read does stay below the width.
Proof sketch: kernel evaluation. -/
theorem star_analysis : ReadAnalysis.analyze 3 starResolved = .certified ⟨0, 3, none,
    [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2)]⟩ := by decide +kernel

/-- The star read resolves to three columns on the original connection and to four after the migration. Proof
sketch: kernel evaluation. -/
theorem star_columns : columnCount initial.connection.resolveState star = 3 ∧
    columnCount reachedConnection.resolveState star = 4 := by decide +kernel

/-- The obligations of the star certificate fail: the star read does not resolve to the certificate's
statement after the migration, because it has a fourth column. Proof sketch: the resolution would have as many
columns as the certificate, which is 3. -/
theorem star_obligations_fail : ¬ (⟨0, 3, none, [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2)]⟩ :
    ReadCertificate).Obligations runContext star initial.connection reachedConnection := by
  intro obligations
  obtain ⟨names, state, resolved⟩ := obligations.resolvesOther
  have count : columnCount reachedConnection.resolveState star = 3 := by
    unfold columnCount
    rw [resolved]
    rfl
  have := star_columns.2
  omega

/-- The claim that the rule would give is false: the outputs of the star read differ before and after the
migration. Proof sketch: kernel evaluation of the two steps. -/
theorem star_outputs_differ :
    (runScriptStep runContext initial.clock 0 initial.connection star []).output ≠
      (runScriptStep runContext initial.clock 1 reachedConnection star []).output := by decide +kernel

-- Metadata after ADD COLUMN

/-- The read of the table's column metadata. -/
def metadata : Syntax.Statement := firstStatement (sql r"PRAGMA table_info(items)")

/-- The analysis gives no certificate for the metadata read. Proof sketch: kernel evaluation. -/
theorem metadata_unknown : analysisUnknown 3 initial.connection.resolveState metadata = true := by decide +kernel

/-- The claim that a certificate would give is false: the metadata lists the new column. Proof sketch:
kernel evaluation of the two steps. -/
theorem metadata_outputs_differ :
    (runScriptStep runContext initial.clock 0 initial.connection metadata []).output ≠
      (runScriptStep runContext initial.clock 1 reachedConnection metadata []).output := by decide +kernel

-- Counter reads

/-- A read whose filter calls {lit}`total_changes()`. -/
def counterRead : Syntax.Statement :=
  firstStatement (sql r"SELECT id FROM items WHERE total_changes() = 1")

/-- The analysis gives no certificate for the counter read: its filter is not calm. Proof sketch: kernel
evaluation. -/
theorem counter_unknown : analysisUnknown 3 initial.connection.resolveState counterRead = true := by
  decide +kernel

/-- The claim that a certificate would give is false: the migration's backfill changes the total number of
changes, so the counter read finds the row before and not after. Proof sketch: kernel evaluation of the steps. -/
theorem counter_outputs_differ :
    (runScriptStep runContext initial.clock 0 initial.connection counterRead []).output ≠
      (runScriptStep runContext initial.clock 1 reachedConnection counterRead []).output := by decide +kernel

#print axioms star_analysis
#print axioms star_columns
#print axioms star_obligations_fail
#print axioms star_outputs_differ
#print axioms metadata_unknown
#print axioms metadata_outputs_differ
#print axioms counter_unknown
#print axioms counter_outputs_differ

end S6RulesNegativeReads
