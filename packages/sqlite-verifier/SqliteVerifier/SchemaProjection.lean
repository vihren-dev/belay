import SqliteVerifier.Library
import Belay.Sqlite.PreservationLaws
import Belay.Sqlite.SchemaClockLaws

set_option doc.verso true

/-! The verification conditions of a schema-only script that keeps one table's projection
(ADR 0013, D8): CREATE TABLE and ADD COLUMN extend every table that they keep
({name}`Belay.Sqlite.runSql_extends`), so the projection of the observed columns stays the
same, and the proof of such a migration only shows that the script succeeds. -/

namespace SqliteVerifier
open Belay.Sqlite

/-- Establish all verification fields for a script of CREATE TABLE and ADD COLUMN
statements ({name}`SchemaOnly`, {name}`ModeledDefinitions`) whose interpretations project
the fields of the table with the name, at the same catalog position before and after
({name}`projectedInterpretation`), with {name}`unreachableFailures`. The caller proves:
* some database is admitted;
* the projection of every valid table that covers the fields satisfies the contract's
  validity;
* in every admitted database, the table at the position covers the fields;
* for every admitted database, the script succeeds with a database that conforms to the
  next catalog and meets the contract's catalog requirement;
* the contract's change relation holds between a value and itself, and its applicability
  holds for every success.
Proof sketch: {name}`VerificationConditions.of_runSql`; the script extends the table at the
position ({name}`runSql_extends`), so the extended table covers the fields and has the same
projection ({name}`TableExtends.covers`, {name}`TableExtends.project`). -/
theorem VerificationConditions.ofSchemaProjection
    {startCatalog nextCatalog : Catalog} {script : List Resolved.Statement}
    {approvedConditions : Database → Prop} {contract : LogicalContract LogicalRows} {profile : Profile}
    {name : String} {fields : List String} {position : Nat}
    (nonempty : ∃ database, Admitted profile startCatalog approvedConditions database)
    (valid : ∀ table, table.Valid → Covers table fields → contract.valid (table.project fields))
    (schema : SchemaOnly script) (modeled : ModeledDefinitions script)
    (startAt : tablePosition startCatalog name = some position)
    (nextAt : tablePosition nextCatalog name = some position)
    (covered : ∀ database, Admitted profile startCatalog approvedConditions database →
      ∃ table, database.table position = some table ∧ Covers table fields)
    (runs : ∀ database, Admitted profile startCatalog approvedConditions database →
      ∃ result, runSql script database = .success result ∧ Conforms profile nextCatalog result ∧
        contract.catalogRequirement result.catalog)
    (change : ∀ logical, contract.change logical logical)
    (applies : ∀ database result, contract.applicability database (.success result)) :
    VerificationConditions startCatalog script approvedConditions contract
      (projectedInterpretation profile startCatalog name fields) (projectedInterpretation profile nextCatalog name fields)
      unreachableFailures profile := by
  apply VerificationConditions.of_runSql nonempty
    (projectedInterpretation_sound contract profile startCatalog name fields valid)
    (projectedInterpretation_sound contract profile nextCatalog name fields valid)
    (unreachableFailures_sound contract profile)
  · intro database admitted
    obtain ⟨table, present, covers⟩ := covered database admitted
    exact ⟨admitted.1, position, table, startAt, present, covers⟩
  · intro database _
    exact SupportedSql.schemaOnly schema modeled
  · intro database admitted
    obtain ⟨result, ran, conforms, required⟩ := runs database admitted
    rw [ran]
    refine ⟨applies database result, ?_⟩
    intro original read
    obtain ⟨table, present, covers⟩ := covered database admitted
    have extended := runSql_extends schema database position table present
    rw [ran] at extended
    obtain ⟨after, stored, growth⟩ := extended
    have tableValid := (admitted.1.2.2.2 position).2 table present
    have same := growth.project (fun row member => (tableValid.2 row member).2.1) covers
    have originalIs : original = table.project fields := by
      simpa [projectedInterpretation, observeTable, startAt, present] using read.symm
    refine ⟨⟨conforms, position, after, nextAt, by simpa [Outcome.database] using stored, growth.covers covers⟩, required, table.project fields, ?_, ?_⟩
    · show observeTable nextCatalog name fields result = some (table.project fields)
      have reached : result.table position = some after := by simpa [Outcome.database] using stored
      simp [observeTable, nextAt, reached, same]
    · rw [originalIs]
      exact change _
  · exact schema.readsClock

end SqliteVerifier
