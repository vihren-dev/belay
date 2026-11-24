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
are the facts about two connections that the migration must give: each step returns the certificate scan and keeps its connection,
and the table that a name finds on the second connection is the table that it finds on the first with cells
appended to each row. The table can sit at another position on the second connection.
{lit}`ReadCertificate.output_eq` then proves that the step of the statement gives the same output on both. A
read that reaches beyond the width, such as a {lit}`SELECT *`, can fail the scan obligation on the second
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
connection. Proof sketch: substitute both witnessed scans and apply the filter and result laws for appended rows. -/
theorem ReadCertificate.output_eq {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.Obligations context statement original other)
    (clock : Option Clock) (originalIndex otherIndex : Nat) (parameters : List Value) :
    (runScriptStep context clock originalIndex original statement parameters).output =
      (runScriptStep context clock otherIndex other statement parameters).output := by
  obtain ⟨beforeNames, before⟩ := obligations.originalScan
  obtain ⟨_, position, table, extended, extra, found, moved, ⟨afterNames, after⟩, scans, wide⟩ := obligations.appended
  rw [before clock originalIndex parameters table (Database.tableNamed_some found).2,
    after clock otherIndex parameters extended (Database.tableNamed_some moved).2]
  simp only [RunStep.output, ReadCertificate.query, ReadCertificate.moved, scans]
  rw [Resolved.Query.simple_results_agree (Resolved.EvalContext.bound parameters) (Resolved.EvalContext.plain_rowFree 0)
    (Resolved.sourceRows table) extra [Resolved.QuerySource.first certificate.position] [Resolved.QuerySource.first position]
    certificate.filter certificate.filter certificate.columns beforeNames afterNames certificate.width wide valid.columnsBelow
    (fun row member => Resolved.Query.filterKeeps_append (Resolved.EvalContext.bound parameters) (Resolved.EvalContext.plain_rowFree 0) row (extra row)
      certificate.width (wide row member) certificate.filter valid.filterBelow)]

/-- For every clock, index and parameters on a connection with the certified table,
a witnessed scan has one execution which keeps the connection. Proof sketch: use the
scan at these inputs and take its row output. -/
theorem ReadCertificate.step_keeps {certificate : ReadCertificate} {context : ResolveContext}
    {statement : Syntax.Statement} {connection : Connection} {table : Table}
    (scan : certificate.Scans context statement connection)
    (present : connection.state.database.table certificate.position = some table)
    (clock : Option Clock) (index : Nat) (parameters : List Value) :
    ∃ output, runScriptStep context clock index connection statement parameters = .continued output connection [] := by
  obtain ⟨names, runs⟩ := scan
  exact ⟨_, runs clock index parameters table present⟩

end Belay.Sqlite
