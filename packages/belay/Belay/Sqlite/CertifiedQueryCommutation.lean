import Belay.Sqlite.ReadCertificatePreservation
import Belay.Sqlite.MigrationQueryFrames

set_option doc.verso true

/-!
Full commutation of a certified read with a migration (ADR 0017, S6). Preservation
({lit}`ReadCertificate.preservesAt`) compares only values and outputs. Commutation also compares the
final connection and the statement count of the two orders, so it needs two more facts, which this
module proves for a certified read. First, a certified read keeps the connection: its step continues, has one
execution and ends at the connection where it started, also when the read fails. Second, the read counts
no change. The module does not prove that the migration reaches one connection with one output count; the
caller gives that fact as a premise ({lit}`uniform`), and the premise holds for a sent script
({lit}`sendStatements_branch_shape`). The clock must give one date at every index, because a read that
moves the statement index must not change the migration.
-/

namespace Belay.Sqlite
open Model

/-- For every valid certificate, statement resolution and present table: the step of the statement continues,
has no execution other than its own, and ends at the connection where it started. In plain words, a
certified read is read-only. Proof sketch: the step does not stop, because its output is a list of rows
({name}`runScriptStep_simpleTable_output`), and a continuing read-only step keeps the connection
({name}`runScriptStep_readOnly_keeps`). -/
theorem ReadCertificate.step_keeps {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {connection : Connection}
    {names : List String} {state : ResolveState} {table : Table}
    (resolved : resolveStatement context connection.resolveState statement =
      .ok (certificate.statement names, state))
    (present : connection.state.database.table certificate.position = some table)
    (clock : Option Clock) (index : Nat) (parameters : List Value) :
    ∃ output, runScriptStep context clock index connection statement parameters = .continued output connection [] := by
  have rows := runScriptStep_simpleTable_output context clock index connection statement parameters
    certificate.position table certificate.filter certificate.columns names resolved present
    (valid.statement_calm names)
  cases step : runScriptStep context clock index connection statement parameters with
  | ended reason => rw [step] at rows; cases rows
  | continued output next others =>
    obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps resolved (Or.inl ⟨_, _, rfl⟩) step
    exact ⟨output, rfl⟩

/-- For every statement and values, and step that continues with no other execution and keeps the
connection: every branch of the program that sends the statement is the run with one selected output, at the
same connection, and returns that output as its value. In plain words, such a program ends at the connection
where it started, returns a value, and has exactly one output. Proof sketch: invert the branch with
{name}`Sql.branch_continued_iff` and {name}`Sql.branch_pure_iff`; the continuation is a pure program. -/
theorem sendStatements_single_keeps {statement : Syntax.Statement} {values : List Value} {clock : Option Clock}
    {index : Nat} {connection : Connection} {output : Output}
    (step : runScriptStep runContext clock index connection statement values = .continued output connection [])
    (branch : SqlRun (List Output)) (ran : (sendStatements [(statement, values)]).Branch clock index connection branch) :
    ∃ selected, branch = { outputs := [selected], connection, value := some [selected] } := by
  have program : sendStatements [(statement, values)] = .exec statement values (fun output => .pure [output]) := rfl
  rw [program] at ran
  obtain ⟨selected, later, -, tail, rfl⟩ := (Sql.branch_continued_iff step branch).mp ran
  obtain rfl := (Sql.branch_pure_iff _ _ _ _ _).mp tail
  exact ⟨selected, rfl⟩

/-- For every migration, valid certificate, statement with values, predicate and premises below, the read of
the statement commutes fully with the migration ({name}`Migration.CommutesOn`). In plain words, at every
context where the predicate holds and the migration succeeds, running the read and then the migration, and
running the migration and then the read, return the same value and visible outputs, reach the same
complete connection and take the same number of statements, on every branch. At a context where the
predicate is false or the migration fails, the conclusion requires nothing. The premises are:
* All branches of the migration reach one connection with one output count ({lit}`uniform`).
* After every branch of the migration, the obligations of the certificate hold between the connection
  before the migration and the connection after it ({lit}`obligations`).
* The clock gives one date at every index at the contexts of the predicate ({lit}`constant`).
* The predicate holds again after the read, at the context with one more statement and one more output
  ({lit}`admittedKept`).
Proof sketch: the obligations give preservation ({name}`ReadCertificate.preservesAt`) at the connection of
the actual run. The read keeps the connection, on the original and on the reached connection
({name}`ReadCertificate.step_keeps`, {name}`sendStatements_single_keeps`), and has one output on each,
which gives {name}`Migration.QueryFrames`; {name}`Migration.TranslatesOn.commutes_of_query` concludes. -/
theorem ReadCertificate.commutesOn {μ : Type} (migration : Sql μ) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop)
    (uniform : ∀ state, Migration.Domain migration admitted state → ∀ one other,
      migration.Branch state.clock state.index state.connection one →
      migration.Branch state.clock state.index state.connection other →
        one.connection = other.connection ∧ one.outputs.length = other.outputs.length)
    (obligations : ∀ state, Migration.Domain migration admitted state → ∀ ran,
      migration.Branch state.clock state.index state.connection ran →
        certificate.Obligations runContext statement state.connection ran.connection)
    (constant : ∀ state, admitted state → ∀ assignment ∈ state.clock, ∀ one other, assignment one = assignment other)
    (admittedKept : ∀ state, Migration.Domain migration admitted state → ∀ selected,
      admitted { state with index := state.index + 1, outputs := state.outputs ++ [selected] }) :
    Migration.CommutesOn migration admitted (send ⟨[(statement, values)]⟩) := by
  have translation : Migration.TranslatesOn migration admitted (send ⟨[(statement, values)]⟩)
      (send ⟨[(statement, values)]⟩) := fun state =>
    ReadCertificate.preservesAt migration valid statement values admitted state
      (migration.runFrom state.clock state.index state.connection).outputs.length
      (migration.runFrom state.clock state.index state.connection).connection
      (fun domain branch ran => uniform state domain branch _ ran
        (Sql.Branch.actual migration state.clock state.index state.connection))
      (fun domain => obligations state domain _ (Sql.Branch.actual migration state.clock state.index state.connection))
  have stepOriginal : ∀ state, Migration.Domain migration admitted state → ∀ ran,
      migration.Branch state.clock state.index state.connection ran →
        ∃ output, runScriptStep runContext state.clock state.index state.connection statement values =
          .continued output state.connection [] := by
    intro state domain ran ran'
    obtain ⟨names, resolved, resolvedOriginal⟩ := (obligations state domain ran ran').resolvesOriginal
    obtain ⟨table, extended, extra, present, -⟩ := (obligations state domain ran ran').appended
    exact ReadCertificate.step_keeps valid resolvedOriginal present state.clock state.index values
  have stepOther : ∀ state, Migration.Domain migration admitted state → ∀ ran,
      migration.Branch state.clock state.index state.connection ran →
        ∃ output, runScriptStep runContext state.clock (state.index + ran.outputs.length) ran.connection statement
          values = .continued output ran.connection [] := by
    intro state domain ran ran'
    obtain ⟨names, resolved, resolvedOther⟩ := (obligations state domain ran ran').resolvesOther
    obtain ⟨table, extended, extra, -, present, -⟩ := (obligations state domain ran ran').appended
    exact ReadCertificate.step_keeps valid resolvedOther present state.clock (state.index + ran.outputs.length) values
  refine Migration.TranslatesOn.commutes_of_query translation ⟨?_, ?_, ?_, ?_⟩ constant uniform
  · intro state domain first branch
    obtain ⟨output, step⟩ := stepOriginal state domain _
      (Sql.Branch.actual migration state.clock state.index state.connection)
    obtain ⟨selected, rfl⟩ := sendStatements_single_keeps step first branch
    exact ⟨rfl, rfl⟩
  · intro state domain ran ran' last branch
    obtain ⟨output, step⟩ := stepOther state domain ran ran'
    obtain ⟨selected, rfl⟩ := sendStatements_single_keeps step last branch
    exact ⟨rfl, rfl⟩
  · intro state domain first ran last firstBranch ran' lastBranch
    obtain ⟨output, step⟩ := stepOriginal state domain _
      (Sql.Branch.actual migration state.clock state.index state.connection)
    obtain ⟨output', step'⟩ := stepOther state domain ran ran'
    obtain ⟨selected, rfl⟩ := sendStatements_single_keeps step first firstBranch
    obtain ⟨other, rfl⟩ := sendStatements_single_keeps step' last lastBranch
    rfl
  · intro state domain first branch
    obtain ⟨output, step⟩ := stepOriginal state domain _
      (Sql.Branch.actual migration state.clock state.index state.connection)
    obtain ⟨selected, rfl⟩ := sendStatements_single_keeps step first branch
    exact admittedKept state domain selected

/-- For every sent script as migration, valid certificate, statement with values, predicate and premises below, the
read of the statement commutes fully with the migration ({name}`Migration.CommutesOn`). The premises are those of
{name}`ReadCertificate.commutesOn`, except that the migration's reached connection is the connection of the
model's run of the script from index 0, so the caller needs no premise about branches and no statement of
the starting index, only that no statement of the script is written as INSERT from a query. Plain words: for every context where the predicate holds and the script succeeds, the
obligations of the certificate hold between the context's connection and the connection that the script
reaches. Proof sketch: every branch of a sent script reaches the connection and the output count of the
model's run ({name}`sendStatements_branch_shape`); a clock with one date at every index makes that
run independent of the start index ({name}`Sql.runFrom_index`); so {name}`ReadCertificate.commutesOn` applies. -/
theorem ReadCertificate.commutesOn_send (script : Script) {certificate : ReadCertificate}
    (valid : certificate.Valid) (statement : Syntax.Statement) (values : List Value)
    (admitted : ExecutionContext → Prop) (single : ∀ entry ∈ script.statements, entry.1.isInsertSelect = false)
    (constant : ∀ state, admitted state → ∀ assignment ∈ state.clock, ∀ one other, assignment one = assignment other)
    (obligations : ∀ state, Migration.Domain (send script) admitted state →
      certificate.Obligations runContext statement state.connection
        (runScriptFrom runContext state.clock 0 state.connection script.statements).connection)
    (admittedKept : ∀ state, Migration.Domain (send script) admitted state → ∀ selected,
      admitted { state with index := state.index + 1, outputs := state.outputs ++ [selected] }) :
    Migration.CommutesOn (send script) admitted (send ⟨[(statement, values)]⟩) := by
  have independent : ∀ state, Migration.Domain (send script) admitted state →
      (runScriptFrom runContext state.clock state.index state.connection script.statements).connection =
        (runScriptFrom runContext state.clock 0 state.connection script.statements).connection := by
    intro state domain
    have := congrArg (fun run : SqlRun (List Output) => run.connection) (Sql.runFrom_index (send script) state.clock (constant state domain.1)
      state.index 0 state.connection)
    simpa [send, Sql.runFrom_send, SqlRun.ofScript] using this
  refine ReadCertificate.commutesOn (send script) valid statement values admitted ?_ ?_ constant admittedKept
  · intro state domain one other oneBranch otherBranch
    obtain ⟨oneConnection, oneLength⟩ := sendStatements_branch_shape _ _ _ _ _
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _ single) oneBranch
    obtain ⟨otherConnection, otherLength⟩ := sendStatements_branch_shape _ _ _ _ _
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _ single) otherBranch
    exact ⟨oneConnection.trans otherConnection.symm, oneLength.trans otherLength.symm⟩
  · intro state domain ran branch
    rw [(sendStatements_branch_shape _ _ _ _ _
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _ single) branch).1, independent state domain]
    exact obligations state domain

end Belay.Sqlite
