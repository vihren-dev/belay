import SchemaStepLaws

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_schema_script_test.py`: a read certificate that survives the drop of an
earlier table (ADR 0017, S6, task {lit}`20261027-schema-script-laws`). In the database of {lit}`SchemaStepLaws` the
child {lit}`c` is at position 1. After {lit}`DROP TABLE p` with foreign keys off it is at position 0 with the same
rows. The certificate of the lookup {lit}`SELECT note FROM c WHERE id = ?1` is for position 1, and its obligations
find the child by its name on the connection after the drop, so the lookup gives the same output on both
connections. The frame law of DROP TABLE gives the table at the new position. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace CertificateAfterDrop
open SchemaStepLaws

/-- The lookup of the note of a child by its id. -/
def lookupStatement : Syntax.Statement := statementOf (sql r"SELECT note FROM c WHERE id = ?1;" .null)

/-- The resolved lookup when the child is at the given position: a simple read that keeps the rows whose column 0
equals parameter 1 and returns column 2. -/
def lookupResolvedAt (position : Nat) : Resolved.Statement :=
  .query (Resolved.Query.simple [Resolved.QuerySource.first position]
    (some (.compare .eq (some .integer) (.column 0) (.parameter 1) .binary)) [.scalar (.column 2)] ["note"]) []

/-- The connection after the drop of the parent, with foreign keys off. -/
def dropped : Connection := (afterStep start dropParent).getD start

/-- The drop continues, and the connection after it is {lean}`dropped`. Proof sketch: the kernel shows that the step
continues; then unfold {name}`afterStep`. -/
theorem dropped_step : ∃ output others, stepOf start dropParent = .continued output dropped others := by
  have continues : (afterStep start dropParent).isSome = true := by decide +kernel
  unfold dropped afterStep at *
  cases step : stepOf start dropParent with
  | continued output next others => exact ⟨output, others, by simp⟩
  | ended reason => simp [step] at continues

/-- The lookup resolves to the read of position 1 on the connection before the drop. Proof sketch: kernel
evaluation. -/
theorem resolves_before : resolvesTo start lookupStatement (lookupResolvedAt 1) = true := by decide +kernel

/-- The lookup resolves to the read of position 0 on the connection after the drop. Proof sketch: kernel
evaluation. -/
theorem resolves_after : resolvesTo dropped lookupStatement (lookupResolvedAt 0) = true := by decide +kernel

/-- The certificate that the untrusted analysis gives for the lookup at the width 3 of the child. -/
def certificate : ReadCertificate :=
  match ReadAnalysis.analyze 3 (lookupResolvedAt 1) with
  | .certified found => found
  | .unknown _ => ⟨0, 0, none, []⟩

/-- The analysis certifies the lookup. Proof sketch: kernel evaluation of the analysis. -/
theorem analysis : ReadAnalysis.analyze 3 (lookupResolvedAt 1) = .certified certificate := by decide +kernel

/-- The certificate is valid. Proof sketch: {name}`ReadAnalysis.analyze_sound`. -/
theorem certificate_valid : certificate.Valid := (ReadAnalysis.analyze_sound analysis).1

/-- The certificate is for the position 1 of the child. -/
theorem certificate_position : certificate.position = 1 := by decide +kernel

/-- The certificate has the width of the child. -/
theorem certificate_width : certificate.width = 3 := by decide +kernel

/-- The moved certificate describes the resolved read at position 0. Proof sketch: kernel evaluation. -/
theorem moved_statement : (certificate.moved 0).statement ["note"] = lookupResolvedAt 0 := by decide +kernel

/-- The obligations of the certificate hold between the connection before the drop and the connection after it.
The child is found by its name at position 1 before and at position 0 after, and the rows are the same (no cell is
appended). Proof sketch: the frame law {name}`runScriptStep_dropTable_frame` gives the table at the new position
with the same rows; the kernel checks that every row has the width. -/
theorem obligations : certificate.Obligations runContext lookupStatement start dropped := by
  refine ⟨ReadAnalysis.resolvesOriginal (resolvesTo_sound resolves_before).choose_spec analysis, ?_⟩
  obtain ⟨after, found⟩ := resolvesTo_sound resolves_after
  obtain ⟨dropAfter, dropFound⟩ := resolvesTo_sound drop_resolves_plain
  obtain ⟨table, present⟩ := tableNamed_exists (database := start.state.database) (name := name! "c") (position := 1)
    (by decide +kernel)
  obtain ⟨output, others, stepped⟩ := dropped_step
  have moved := runScriptStep_dropTable_frame (connection := start) (dropped := name! "p") (ifExists := false) rfl
    dropFound stepped (other := name! "c") (by decide +kernel) present
  have wide : (Resolved.sourceRows table).all (fun row => decide (3 ≤ row.length)) = true := by
    have check : ((start.state.database.tableNamed (name! "c")).map fun (_, t) =>
        (Resolved.sourceRows t).all fun row => decide (3 ≤ row.length)) = some true := by decide +kernel
    rw [present] at check
    exact Option.some.inj check
  refine ⟨name! "c", 0, table, table, fun _ => [], ?_, ?_, ⟨["note"], after, ?_⟩, by simp, ?_⟩
  · rw [certificate_position]; exact present
  · have same : keptBelow [0] 1 = 0 := by decide +kernel
    rw [moved, same]
  · rw [moved_statement]; exact found
  · intro row member
    rw [certificate_width]
    simpa using List.all_eq_true.mp wide row member

/-- For every bound value, the lookup gives the same output before the drop of the parent and after it, at the two
positions of the child. Proof sketch: {name}`ReadCertificate.output_eq` with the obligations above. -/
theorem lookup_output_survives_the_drop (value : Value) (clock : Option Clock) (firstIndex secondIndex : Nat) :
    (runScriptStep runContext clock firstIndex start lookupStatement [value]).output =
      (runScriptStep runContext clock secondIndex dropped lookupStatement [value]).output :=
  ReadCertificate.output_eq certificate_valid obligations clock firstIndex secondIndex [value]

#print axioms obligations
#print axioms lookup_output_survives_the_drop

end CertificateAfterDrop
