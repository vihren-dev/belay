import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.Model

set_option doc.verso true

/-!
Dependency certificates of reads (ADR 0017, S6). A dependency analysis is untrusted: it can say what a
read depends on, but only a checked rule makes the claim true. This module gives the claim and its rule for
reads of one table that use a filter and scalar columns, which are the reads a column-appending migration can
leave unchanged. A {lit}`ReadCertificate` names the table position and the width below which the read looks
at columns. It is {lit}`ReadCertificate.Valid` when the filter and the columns read only columns below the
width and call nothing that can fail, read the clock or read a counter. The {lit}`ReadCertificate.Obligations`
are the facts about two connections that the migration must give: the statement resolves to the read on both,
and the table of the second connection is the table of the first with cells appended to each row.
{lit}`ReadCertificate.output_eq` then proves that the step of the statement gives the same output on both. A
read that reaches beyond the width, such as a {lit}`SELECT *`, fails the resolution obligation on the second
connection, and no certificate holds for it. The certificates say nothing about writes, triggers or
counters. A statement that does not fit the form has no certificate.
-/

namespace Belay.Sqlite
open Model

/-- A certificate for a read of one table: the position of the table, the width of the columns that the
read uses (it uses only columns below the width), and the resolved filter and scalar result columns. For
example, the read of the {lit}`id` column of the rows with {lit}`name = ?1` in a table at position 0, with the
columns {lit}`id, name` at positions 0 and 1, has width 2. -/
structure ReadCertificate where
  /-- The position of the table in the database. -/
  position : Nat
  /-- The read uses only the columns below this number. -/
  width : Nat
  /-- The condition of the read, when it has one. -/
  filter : Option Resolved.Expr
  /-- The result columns of the read. -/
  columns : List Resolved.Output
deriving DecidableEq

/-- The resolved query that a certificate describes, with the given result names: the simple query that
reads the table at the position, keeps the rows where the filter is true, and returns the columns. -/
def ReadCertificate.query (certificate : ReadCertificate) (names : List String) : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first certificate.position] certificate.filter certificate.columns names

/-- The resolved statement that a certificate describes: the query of the certificate with no
subqueries. -/
def ReadCertificate.statement (certificate : ReadCertificate) (names : List String) : Resolved.Statement :=
  .query (certificate.query names) []

/-- A valid certificate. In plain words, it requires three facts:
* The filter, when there is one, reads only columns below the width
  ({name}`Resolved.Expr.readsBelow`).
* Every result column is a scalar expression that reads only columns below the width. An aggregate column
  never does ({name}`Resolved.Output.readsBelow`).
* Every expression of the filter and of the columns is calm ({name}`Resolved.Expr.Calm`): it calls no
  function that can fail and reads no clock and no counter. -/
structure ReadCertificate.Valid (certificate : ReadCertificate) : Prop where
  /-- The filter reads only columns below the width. -/
  filterBelow : ∀ condition ∈ certificate.filter, condition.readsBelow certificate.width = true
  /-- The result columns read only columns below the width. -/
  columnsBelow : ∀ column ∈ certificate.columns, column.readsBelow certificate.width = true
  /-- The filter and the scalar result columns are calm. -/
  calm : ∀ expression ∈ certificate.filter.toList ++ certificate.columns.flatMap Resolved.Output.scalars,
    expression.Calm

/-- For every valid certificate and result names, the statement of the certificate is calm
({name}`Resolved.Statement.Calm`). Proof sketch: a column that reads below a width is scalar, so it has no
operands ({name}`Resolved.Output.operands_of_readsBelow`), and a one-table read with calm parts is calm
({name}`Resolved.Statement.simpleTable_calm`). -/
theorem ReadCertificate.Valid.statement_calm {certificate : ReadCertificate} (valid : certificate.Valid)
    (names : List String) : (certificate.statement names).Calm :=
  Resolved.Statement.simpleTable_calm certificate.position certificate.filter certificate.columns names valid.calm
    fun column member => Resolved.Output.operands_of_readsBelow (valid.columnsBelow column member)

/-- The facts that a migration must give for a read, so that the statement keeps its output from the
original connection to the other connection. In plain words, for a certificate, resolution context and
statement, with two connections:
* The statement resolves on the original connection to the statement of the certificate, with some result names.
* The statement resolves on the other connection to the statement of the certificate, with some result
  names. This fails for a {lit}`SELECT *` after a column is added, because the new resolution has more columns.
* The table at the position exists on both connections, the rows that the other connection scans are those of
  the original connection with cells appended to each row (the cells can depend on the row), and every
  original row has at least as many cells as the width. -/
structure ReadCertificate.Obligations (certificate : ReadCertificate) (context : ResolveContext)
    (statement : Syntax.Statement) (original other : Connection) : Prop where
  /-- The statement resolves to the certificate's statement on the original connection. -/
  resolvesOriginal : ∃ names state,
    resolveStatement context original.resolveState statement = .ok (certificate.statement names, state)
  /-- The statement resolves to the certificate's statement on the other connection. -/
  resolvesOther : ∃ names state,
    resolveStatement context other.resolveState statement = .ok (certificate.statement names, state)
  /-- The two tables are related by appended cells and the original rows are wide enough. -/
  appended : ∃ (table extended : Table) (extra : List Value → List Value),
    original.state.database.table certificate.position = some table ∧
    other.state.database.table certificate.position = some extended ∧
    Resolved.sourceRows extended = (Resolved.sourceRows table).map (fun row => row ++ extra row) ∧
    ∀ row ∈ Resolved.sourceRows table, certificate.width ≤ row.length

/-- For every valid certificate, resolution context, statement, parameters, clocks and statement indexes,
and every two connections that satisfy the obligations of the certificate: the step of the statement on
the original connection and the step on the other connection give the same output. In plain words, a
read that the certificate describes cannot see the cells that the migration appended. The result does
not say that the two steps end at the same connection. Proof sketch: obtain the two resolutions and the
tables from the obligations, and apply {name}`runScriptStep_simpleTable_output_append`. -/
theorem ReadCertificate.output_eq {certificate : ReadCertificate} (valid : certificate.Valid)
    {context : ResolveContext} {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.Obligations context statement original other)
    (clock : Option Clock) (originalIndex otherIndex : Nat) (parameters : List Value) :
    (runScriptStep context clock originalIndex original statement parameters).output =
      (runScriptStep context clock otherIndex other statement parameters).output := by
  obtain ⟨names, state, resolvedOriginal⟩ := obligations.resolvesOriginal
  obtain ⟨others, otherState, resolvedOther⟩ := obligations.resolvesOther
  obtain ⟨table, extended, extra, presentOriginal, presentOther, scans, wide⟩ := obligations.appended
  exact runScriptStep_simpleTable_output_append context clock originalIndex otherIndex original other statement
    parameters certificate.position table extended certificate.filter certificate.columns names others
    certificate.width extra resolvedOriginal resolvedOther presentOriginal presentOther
    (valid.statement_calm names) scans wide valid.filterBelow valid.columnsBelow

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
for the original connection, with the second resolution of the obligations. -/
theorem ReadCertificate.Obligations.single_other {certificate : ReadCertificate} {context : ResolveContext}
    {statement : Syntax.Statement} {original other : Connection}
    (obligations : certificate.Obligations context statement original other) :
    ∀ resolved after, resolveStatement context other.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false := by
  obtain ⟨names, state, found⟩ := obligations.resolvesOther
  intro resolved after again
  rw [found] at again
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj again)
  rfl

end Belay.Sqlite
