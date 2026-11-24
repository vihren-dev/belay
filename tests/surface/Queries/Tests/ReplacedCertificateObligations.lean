import Belay

set_option doc.verso true

/-! ADR 0033 retention of the original structural read obligations and their consequences. -/

namespace Belay.Sqlite
open Model

/-- The facts that a migration must give for a read, so that the statement keeps its output from the
original connection to the other connection. In plain words, for a certificate, resolution context and
statement, with two connections:
* The statement resolves on the original connection to the statement of the certificate, with some result names.
* There is a table name, a position and two tables such that the name finds, on the original connection,
  the table at the position of the certificate, and on the other connection the second table at the
  given other position ({name}`Model.Database.tableNamed`). The two positions can differ.
* The statement resolves on the other connection to the statement of the certificate at the other position,
  with some result names. This fails for a {lit}`SELECT *` after a column is added, because the new
  resolution has more columns.
* The rows that the other connection scans are those of the original connection with cells appended to
  each row (the cells can depend on the row), and every original row has at least as many cells as the width. -/
structure ReadCertificate.OriginalObligations (certificate : ReadCertificate) (context : ResolveContext)
    (statement : Syntax.Statement) (original other : Connection) : Prop where
  /-- The statement resolves to the certificate's statement on the original connection. -/
  resolvesOriginal : ∃ names state,
    resolveStatement context original.resolveState statement = .ok (certificate.statement names, state)
  /-- A name finds the two tables, the statement resolves to the read of the second table, and the two
  tables are related by appended cells with original rows wide enough. -/
  appended : ∃ (name : Identifier) (otherPosition : Nat) (table extended : Table)
      (extra : List Value → List Value),
    original.state.database.tableNamed name = some (certificate.position, table) ∧
    other.state.database.tableNamed name = some (otherPosition, extended) ∧
    (∃ names state, resolveStatement context other.resolveState statement =
      .ok ((certificate.moved otherPosition).statement names, state)) ∧
    Resolved.sourceRows extended = (Resolved.sourceRows table).map (fun row => row ++ extra row) ∧
    ∀ row ∈ Resolved.sourceRows table, certificate.width ≤ row.length

/-- A valid certificate's original resolution is sufficient to witness its scan.
Proof sketch: select the query equation and simplify its six scan checks. -/
theorem ReadCertificate.original_scan {witness : ReadCertificate} (valid : witness.Valid) {context : ResolveContext}
    {statement : Syntax.Statement} {connection : Connection} {names state}
    (resolved : resolveStatement context connection.resolveState statement = .ok (witness.statement names, state)) :
    witness.Scans context statement connection := by
  refine ⟨names, ?_⟩
  intro clock index parameters table present
  have calm := valid.statement_calm names
  change (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.first witness.position]
    witness.filter witness.columns names) []).Calm at calm
  change resolveStatement _ _ _ = .ok (.query (witness.query names) [], _) at resolved
  rw [runScriptStep_query_eq resolved]
  simp [statementClock, calm.readsClock, calm.counterReads, ReadCertificate.query,
    Resolved.Query.simpleTable_checks parameters present calm, List.eraseDups_cons,
    Resolved.stableSort, Resolved.insertStable]

/-- Both original resolver checks supply actual scan witnesses, with the same table relation. -/
theorem ReadCertificate.OriginalObligations.scans {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {original other : Connection}
    (old : certificate.OriginalObligations context statement original other) :
    certificate.Obligations context statement original other := by
  obtain ⟨_, _, first⟩ := old.resolvesOriginal
  obtain ⟨name, position, table, extended, extra, found, moved, ⟨_, _, last⟩, rows, wide⟩ := old.appended
  exact ⟨ReadCertificate.original_scan valid first, name, position, table, extended, extra, found, moved,
    ReadCertificate.original_scan (valid.moved _) last, rows, wide⟩

/-- For every certificate, context, statement and two connections that satisfy the obligations of the
certificate: the statement resolves on the original connection to no INSERT from a query without rules
({name}`Resolved.Statement.fromQuery`), so a step of it that continues has no further execution
({name}`runScriptStep_others`). A step may still end the run, for a missing clock value or an unknown
counter. Proof sketch: every resolution of the statement is the query statement of the certificate, which
is no INSERT. -/
theorem ReadCertificate.OriginalObligations.single_original {certificate : ReadCertificate} {context : ResolveContext}
    {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.OriginalObligations context statement original other) :
    ∀ resolved after, resolveStatement context original.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false := by
  obtain ⟨names, state, found⟩ := obligations.resolvesOriginal
  intro resolved after again
  rw [found] at again
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj again)
  rfl

/-- The same for the other connection ({name}`ReadCertificate.OriginalObligations.single_original`). Proof sketch: as
for the original connection, with the resolution at the other position from the obligations. -/
theorem ReadCertificate.OriginalObligations.single_other {certificate : ReadCertificate} {context : ResolveContext}
    {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.OriginalObligations context statement original other) :
    ∀ resolved after, resolveStatement context other.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false := by
  obtain ⟨_, _, _, _, _, _, _, ⟨names, state, found⟩, _⟩ := obligations.appended
  intro resolved after again
  rw [found] at again
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj again)
  rfl

/-- The former {lit}`step_keeps` follows for its original resolver premise. -/
theorem ReadCertificate.original_step_keeps {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {connection : Connection}
    {names : List String} {state : ResolveState} {table : Table}
    (resolved : resolveStatement context connection.resolveState statement =
      .ok (certificate.statement names, state))
    (present : connection.state.database.table certificate.position = some table)
    (clock : Option Clock) (index : Nat) (parameters : List Value) :
    ∃ output, runScriptStep context clock index connection statement parameters = .continued output connection [] :=
  ReadCertificate.step_keeps (ReadCertificate.original_scan valid resolved) present clock index parameters

#print axioms ReadCertificate.original_step_keeps
#print axioms ReadCertificate.OriginalObligations.single_original
#print axioms ReadCertificate.OriginalObligations.single_other

end Belay.Sqlite
