import ReplacedCertificateObligations

set_option doc.verso true

/-! Original migration and observation claims for structurally certified reads. -/

namespace Belay.Sqlite
open Model

/-- The original {lit}`output_eq` contract follows by checking the two scans. -/
theorem ReadCertificate.original_output_eq {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.OriginalObligations context statement original other)
    (clock : Option Clock) (originalIndex otherIndex : Nat) (parameters : List Value) :
    (runScriptStep context clock originalIndex original statement parameters).output =
      (runScriptStep context clock otherIndex other statement parameters).output :=
  ReadCertificate.output_eq valid (obligations.scans valid) clock originalIndex otherIndex parameters

/-- The original preservesAt contract follows by checking the two scans. -/
theorem ReadCertificate.original_preservesAt {μ : Type} (migration : Sql μ) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop) (state : ExecutionContext)
    (obligations : Migration.Domain migration admitted state → ∀ branch,
      migration.Branch state.clock state.index state.connection branch →
        certificate.OriginalObligations runContext statement state.connection branch.connection) :
    Migration.PreservesAt migration admitted (send ⟨[(statement, values)]⟩) state :=
  ReadCertificate.preservesAt migration valid statement values admitted state fun domain branch ran =>
    (obligations domain branch ran).scans valid

/-- The original {lit}`preservesAt_send` contract follows by checking the two scans. -/
theorem ReadCertificate.original_preservesAt_send (script : Script) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop) (state : ExecutionContext)
    (single : ∀ entry ∈ script.statements, entry.1.isInsertSelect = false)
    (obligations : Migration.Domain (send script) admitted state →
      certificate.OriginalObligations runContext statement state.connection
        (runScriptFrom runContext state.clock state.index state.connection script.statements).connection) :
    Migration.PreservesAt (send script) admitted (send ⟨[(statement, values)]⟩) state :=
  ReadCertificate.preservesAt_send script valid statement values admitted state single fun domain =>
    (obligations domain).scans valid

/-- The original commutesOn contract follows by checking the two scans. -/
theorem ReadCertificate.original_commutesOn {μ : Type} (migration : Sql μ) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop)
    (uniform : ∀ state, Migration.Domain migration admitted state → ∀ one other,
      migration.Branch state.clock state.index state.connection one →
      migration.Branch state.clock state.index state.connection other →
        one.connection = other.connection ∧ one.outputs.length = other.outputs.length)
    (obligations : ∀ state, Migration.Domain migration admitted state → ∀ ran,
      migration.Branch state.clock state.index state.connection ran →
        certificate.OriginalObligations runContext statement state.connection ran.connection)
    (constant : ∀ state, admitted state → ∀ assignment ∈ state.clock, ∀ one other, assignment one = assignment other)
    (admittedKept : ∀ state, Migration.Domain migration admitted state → ∀ selected,
      admitted { state with index := state.index + 1, outputs := state.outputs ++ [selected] }) :
    Migration.CommutesOn migration admitted (send ⟨[(statement, values)]⟩) :=
  ReadCertificate.commutesOn migration valid statement values admitted uniform
    (fun state domain ran branch => (obligations state domain ran branch).scans valid) constant admittedKept

/-- The original {lit}`commutesOn_send` contract follows by checking the two scans. -/
theorem ReadCertificate.original_commutesOn_send (script : Script) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop) (single : ∀ entry ∈ script.statements, entry.1.isInsertSelect = false)
    (constant : ∀ state, admitted state → ∀ assignment ∈ state.clock, ∀ one other, assignment one = assignment other)
    (obligations : ∀ state, Migration.Domain (send script) admitted state →
      certificate.OriginalObligations runContext statement state.connection
        (runScriptFrom runContext state.clock 0 state.connection script.statements).connection)
    (admittedKept : ∀ state, Migration.Domain (send script) admitted state → ∀ selected,
      admitted { state with index := state.index + 1, outputs := state.outputs ++ [selected] }) :
    Migration.CommutesOn (send script) admitted (send ⟨[(statement, values)]⟩) :=
  ReadCertificate.commutesOn_send script valid statement values admitted single constant
    (fun state domain => (obligations state domain).scans valid) admittedKept

#print axioms ReadCertificate.original_output_eq
#print axioms ReadCertificate.original_preservesAt
#print axioms ReadCertificate.original_preservesAt_send
#print axioms ReadCertificate.original_commutesOn
#print axioms ReadCertificate.original_commutesOn_send

end Belay.Sqlite
