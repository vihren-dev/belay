import Belay.Sqlite.ReadCertificate
import Belay.Sqlite.SendStatementsBranches
import Belay.Sqlite.SingleStatementObservations
import Belay.Sqlite.MigrationPatternAfter

set_option doc.verso true

/-!
Preservation of a certified read by a migration (ADR 0017, S6). Preservation is the weak claim: the
read before the migration and the same read after it give the same value, the same visible outputs and the
same set of branch observations. It says nothing about the final connection, the statement index or the
counters, so it is not commutation. Full commutation is a separate rule
({lit}`ReadCertificate.commutesOn` in {lit}`CertifiedQueryCommutation`). The rules here do not look into the migration: the
caller gives the connection that the migration reaches and the obligations of the certificate for it. For a
migration that is a sent script, the reached connection is the model's run of the script.
-/

namespace Belay.Sqlite
open Model

/-- For every migration, valid certificate, statement with values, predicate and context: if, whenever the
migration succeeds at the context, all its branches reach one connection with one count of outputs, and the
obligations of the certificate hold between the context's connection and that reached connection, then the
read of the statement is preserved by the migration at the context ({name}`Migration.PreservesAt`).
In plain words, at a context where the predicate holds and the migration succeeds on every branch, the
statement before the migration and after it give equal values and visible outputs on the actual run and
on every raw and concrete branch. At any other context the claim requires nothing. Proof sketch: the
obligations give equal step outputs ({name}`ReadCertificate.output_eq`), so the actual observations
and the sets of branch observations are equal ({name}`sendStatements_single_observations`), and
{name}`Migration.translatesAt_of_observations` turns them into preservation. -/
theorem ReadCertificate.preservesAt {μ : Type} (migration : Sql μ) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop) (state : ExecutionContext) (count : Nat) (reached : Connection)
    (uniform : Migration.Domain migration admitted state → ∀ branch,
      migration.Branch state.clock state.index state.connection branch →
        branch.connection = reached ∧ branch.outputs.length = count)
    (obligations : Migration.Domain migration admitted state →
      certificate.Obligations runContext statement state.connection reached) :
    Migration.PreservesAt migration admitted (send ⟨[(statement, values)]⟩) state := by
  intro domain
  obtain ⟨actual, branches⟩ := sendStatements_single_observations statement statement values values state.clock
    state.clock state.index (state.index + count) state.connection reached
    (obligations domain).single_original (obligations domain).single_other
    (ReadCertificate.output_eq valid (obligations domain) state.clock state.index (state.index + count) values)
  exact Migration.translatesAt_of_observations migration _ _ state count reached domain.2 (uniform domain)
    actual branches

/-- For every sent script as migration, valid certificate, statement with values, predicate and context: if,
whenever the migration succeeds at the context, the obligations of the certificate hold between the
context's connection and the connection of the model's run of the script, then the read is preserved by
the migration at the context. In plain words, the reached connection is the connection of the model's run,
so the caller needs no premise about branches, only that no statement of the script is written as INSERT
from a query ({name}`ScriptConditionsWith.of_not_insertSelect`). Proof sketch: every branch of a sent script reaches the
connection and the output count of the model's run ({name}`sendStatements_branch_shape`), so
{name}`ReadCertificate.preservesAt` applies. -/
theorem ReadCertificate.preservesAt_send (script : Script) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop) (state : ExecutionContext)
    (single : ∀ entry ∈ script.statements, entry.1.isInsertSelect = false)
    (obligations : Migration.Domain (send script) admitted state →
      certificate.Obligations runContext statement state.connection
        (runScriptFrom runContext state.clock state.index state.connection script.statements).connection) :
    Migration.PreservesAt (send script) admitted (send ⟨[(statement, values)]⟩) state :=
  ReadCertificate.preservesAt (send script) valid statement values admitted state
    (runScriptFrom runContext state.clock state.index state.connection script.statements).outputs.length
    (runScriptFrom runContext state.clock state.index state.connection script.statements).connection
    (fun _ branch reached => sendStatements_branch_shape _ _ _ _ branch
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _ single) reached) obligations

end Belay.Sqlite
