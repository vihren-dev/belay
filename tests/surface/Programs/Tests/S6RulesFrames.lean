import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: the frame rules of ADR 0017, S6, used on a program. A script
of a plain write to the audit table and a read, followed by a continuation that depends on the output of the
read, keeps the catalog, the items table, the settings and the snapshot of an open transaction on every branch.
The read has two permitted results, and the continuation writes the audit table. The package holds only the
general rules. The tables, statements and claims are part of this fixture. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesFrames
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The values of the rows of the table at a position. -/
def tableValues (position : Nat) (connection : Connection) : List (List Value) :=
  (connection.state.database.rowsAt position).map (·.values)

/-- Whether the statement, when it resolves at the state, resolves to a statement that the shelter rule
covers: a plain write to a table other than the position, a query or a prepare error. A statement that does not
resolve is covered. -/
def shelterAccepted (position : Nat) (state : ResolveState) (statement : Syntax.Statement) : Bool :=
  match resolveStatement runContext state statement with
  | .ok (.query _ _, _) | .ok (.prepareError _, _) => true
  | .ok (resolved, _) => resolved.plainWriteTarget.any (· != position)
  | .error _ => true

/-- If the check succeeds, the statement is sheltered from the position at the state. Proof sketch: invert the
check; each accepted resolution is one of the three shapes of {name}`Resolved.Statement.ShelteredFrom`. -/
theorem shelterAccepted_sound {position : Nat} {state : ResolveState} {statement : Syntax.Statement}
    (accepted : shelterAccepted position state statement = true) : statement.ShelteredAt position state := by
  intro resolved after found
  unfold shelterAccepted at accepted
  split at accepted
  · rename_i query subqueries _ same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (same.symm.trans found))
    exact Or.inr (Or.inl ⟨query, subqueries, rfl⟩)
  · rename_i error _ same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (same.symm.trans found))
    exact Or.inr (Or.inr ⟨error, rfl⟩)
  · rename_i resolvedAgain afterAgain _ _ same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (same.symm.trans found))
    cases target : resolvedAgain.plainWriteTarget with
    | none => simp [target] at accepted
    | some at_ =>
      simp only [target, Option.any_some, bne_iff_ne, ne_eq] at accepted
      exact Or.inl ⟨at_, target, accepted⟩
  · rename_i same
    rw [same] at found
    cases found

/-- Two items, so that a read of one item has two permitted results. -/
def busy : Database := db! r"
  CREATE TABLE items(id INTEGER PRIMARY KEY, qty INTEGER);
  CREATE TABLE audit(note TEXT);
  INSERT INTO items VALUES(1, 5);
  INSERT INTO items VALUES(2, 7);"

/-- A complete environment with a constant clock. -/
def environment : Env :=
  { clock := some (fun _ => 0), counters := Counters.newConnection }

/-- The context after the statement BEGIN: a transaction is open, and its snapshot is the database of the start. -/
def inTransaction : ExecutionContext :=
  { clock := environment.clock, index := 1
    connection := (runScriptFrom runContext environment.clock 0
      (ExecutionContext.initial busy environment).connection (sql r"BEGIN").statements).connection }

/-- A script that writes the audit table and then reads one item without an order. -/
def scan : Script := sql r"INSERT INTO audit VALUES('scan'); SELECT id FROM items LIMIT 1"

/-- The write of an id to the audit table. -/
def logId (id : Value) : Script := sql r"INSERT INTO audit VALUES (?1)" id

/-- The one statement of {name}`logId`. -/
def logStatement : Syntax.Statement := ((logId .null).statements.head (by decide +kernel)).1

/-- The script {name}`logId` sends its statement with the value. Proof sketch: by definition. -/
theorem logId_statements (id : Value) : (logId id).statements = [(logStatement, [id])] := rfl

/-- The program: scan, then write the id that the read chose to the audit table. The next statement depends on
the output of the read, which has two permitted results. -/
def scanThenLog : Sql (List Output) :=
  (send scan).bind fun outputs =>
    match outputs with
    | [_, .rows [[id]]] => send (logId id)
    | _ => send (logId .null)

/-- The read of {name}`scan` has two permitted results, so the program has a branch for each. Proof sketch:
kernel evaluation of the outputs of the run. -/
theorem scan_has_two_results :
    (runScriptFrom runContext inTransaction.clock inTransaction.index inTransaction.connection scan.statements).outputs =
      [.done 1, .oneOf [[[.integer 1]], [[.integer 2]]]] := by
  decide +kernel

/-- The statements of {name}`scan` are sheltered from the items table. Proof sketch: kernel evaluation of the
check. -/
theorem scan_sheltered : ∀ entry ∈ scan.statements,
    entry.1.ShelteredAt 0 inTransaction.connection.resolveState := by
  have accepted : ∀ entry ∈ scan.statements,
      shelterAccepted 0 inTransaction.connection.resolveState entry.1 = true := by decide +kernel
  exact fun entry member => shelterAccepted_sound (accepted entry member)

/-- The write of an id is sheltered from the items table at every state with the resolution state of
{name}`inTransaction`, for every id. Proof sketch: kernel evaluation of the check for the one statement. -/
theorem logId_sheltered (id : Value) (state : ExecutionContext)
    (same : state.connection.resolveState = inTransaction.connection.resolveState) :
    (send (logId id)).Frame (Connection.shelter 0) state := by
  have accepted : shelterAccepted 0 inTransaction.connection.resolveState logStatement = true := by
    decide +kernel
  refine Sql.Frame.sendStatements_sheltered 0 _ state fun entry member => ?_
  rw [logId_statements, List.mem_singleton] at member
  subst member
  rw [same]
  exact shelterAccepted_sound accepted

/-- On every branch of the program, the catalog, the items table, the snapshot of the open transaction and the
two settings are the same as at the start, whichever of the two results the read chooses. In plain words, the
program writes only the audit table. Proof sketch: {name}`Sql.Frame.bind` joins the frame of the script
({name}`Sql.Frame.sendStatements_sheltered`, with {name}`scan_sheltered`) and the frame of the continuation; the
continuation resolves at the same state as the start because the script kept the shelter
({name}`Connection.shelter_resolveState`), and {name}`logId_sheltered` gives its frame for every id. -/
theorem scanThenLog_keeps_shelter : scanThenLog.Frame (Connection.shelter 0) inTransaction := by
  have first := Sql.Frame.sendStatements_sheltered 0 scan.statements inTransaction scan_sheltered
  refine Sql.Frame.bind first fun ran branch value _ => ?_
  have same : (inTransaction.finish ran).connection.resolveState = inTransaction.connection.resolveState :=
    Connection.shelter_resolveState (first ran branch)
  show (match value with | [_, .rows [[id]]] => send (logId id) | _ => send (logId .null)).Frame _ _
  split <;> exact logId_sheltered _ _ same

/-- On every branch of the program, the snapshot of the open transaction is the snapshot at the start, and the
transaction is still open. Proof sketch: the snapshot is a part of the shelter of
{name}`scanThenLog_keeps_shelter`; kernel evaluation shows that the transaction is open at the start. -/
theorem scanThenLog_keeps_transaction (result : SqlRun (List Output))
    (branch : scanThenLog.Branch inTransaction.clock inTransaction.index inTransaction.connection result) :
    result.connection.state.snapshot = inTransaction.connection.state.snapshot ∧
      result.connection.state.snapshot.isSome = true := by
  have kept : result.connection.state.snapshot = inTransaction.connection.state.snapshot :=
    congrArg (fun shelter => shelter.2.2.1) (scanThenLog_keeps_shelter result branch)
  refine ⟨kept, ?_⟩
  rw [kept]
  decide +kernel

/-- The program writes a table that it does not shelter: the audit table at position 1 changes on the actual
run, so the frame claim of the audit table is false. This shows that the shelter claim is not empty, because it
is about the items table only. Proof sketch: kernel evaluation of the actual run. -/
theorem scanThenLog_writes_audit : ¬ scanThenLog.Frame (tableValues 1) inTransaction := by
  intro frame
  have same := frame _ (Sql.Branch.actual _ _ _ _)
  revert same
  decide +kernel

#print axioms shelterAccepted_sound
#print axioms scan_has_two_results
#print axioms scan_sheltered
#print axioms logId_sheltered
#print axioms scanThenLog_keeps_shelter
#print axioms scanThenLog_keeps_transaction
#print axioms scanThenLog_writes_audit

end S6RulesFrames
