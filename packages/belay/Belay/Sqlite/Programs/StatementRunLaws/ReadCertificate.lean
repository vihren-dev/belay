import Belay.Sqlite.Programs.Claims.ExecutionStep
import Belay.Sqlite.Schema.Dispatch.ReadCertificate

set_option doc.verso true

/-!
Dependency certificates of reads (ADR 0017, S6). A dependency analysis is untrusted: it can say what a
read depends on, but only a checked rule makes the claim true. This module gives the claim and its rule for
reads of one table that use a filter and scalar columns, which are the reads a column-appending migration can
leave unchanged. A {lit}`ReadCertificate` names the table position and the width below which the read looks
at columns. It is {lit}`ReadCertificate.Valid` when the filter and the columns read only columns below the
width and call nothing that can fail, read the clock or read a counter. The {lit}`ReadCertificate.Obligations`
are the facts about two connections that the migration must give: the statement resolves to the read on both,
and the table that a name finds on the second connection is the table that it finds on the first with cells
appended to each row. The table can sit at another position on the second connection.
{lit}`ReadCertificate.output_eq` then proves that the step of the statement gives the same output on both. A
read that reaches beyond the width, such as a {lit}`SELECT *`, fails the resolution obligation on the second
connection, and no certificate holds for it. The certificates say nothing about writes, triggers or
counters. A statement that does not fit the form has no certificate.
-/

namespace Belay.Sqlite
open Model

/-- For every valid certificate, resolution context, statement, parameters, clocks and statement indexes,
and every two connections that satisfy the obligations of the certificate: the step of the statement on
the original connection and the step on the other connection give the same output. In plain words, a
read that the certificate describes cannot see the cells that the migration appended, and cannot see
that the table moved to another position. The result does not say that the two steps end at the same
connection. Proof sketch: obtain the two resolutions and the tables from the obligations, and apply
{name}`runScriptStep_simpleTable_output_append`. -/
theorem ReadCertificate.output_eq {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.Obligations context statement original other)
    (clock : Option Clock) (originalIndex otherIndex : Nat) (parameters : List Value) :
    (runScriptStep context clock originalIndex original statement parameters).output =
      (runScriptStep context clock otherIndex other statement parameters).output := by
  obtain ⟨names, state, resolvedOriginal⟩ := obligations.resolvesOriginal
  obtain ⟨name, otherPosition, table, extended, extra, foundOriginal, foundOther, ⟨others, otherState, resolvedOther⟩,
    scans, wide⟩ := obligations.appended
  exact runScriptStep_simpleTable_output_append context clock originalIndex otherIndex original other statement
    parameters name certificate.position otherPosition table extended certificate.filter certificate.columns names
    others certificate.width extra foundOriginal foundOther resolvedOriginal resolvedOther
    (valid.statement_calm names) ((valid.moved otherPosition).statement_calm others) scans wide valid.filterBelow
    valid.columnsBelow

/-- For every certificate, context, statement and two connections that satisfy the obligations of the
certificate: the statement resolves on the original connection to no INSERT from a query without rules
({name}`Resolved.Statement.fromQuery`), so a step of it that continues has no further execution
({name}`runScriptStep_others`). A step may still end the run, for a missing clock value or an unknown
counter. Proof sketch: every resolution of the statement is the query statement of the certificate, which
is no INSERT. -/
theorem ReadCertificate.Obligations.single_original {certificate : ReadCertificate} {context : ResolveContext}
    {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.Obligations context statement original other) :
    ∀ resolved after, resolveStatement context original.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false := by
  obtain ⟨names, state, found⟩ := obligations.resolvesOriginal
  intro resolved after again
  rw [found] at again
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj again)
  rfl

/-- The same for the other connection ({name}`ReadCertificate.Obligations.single_original`). Proof sketch: as
for the original connection, with the resolution at the other position from the obligations. -/
theorem ReadCertificate.Obligations.single_other {certificate : ReadCertificate} {context : ResolveContext}
    {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.Obligations context statement original other) :
    ∀ resolved after, resolveStatement context other.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false := by
  obtain ⟨_, _, _, _, _, _, _, ⟨names, state, found⟩, _⟩ := obligations.appended
  intro resolved after again
  rw [found] at again
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj again)
  rfl

end Belay.Sqlite
