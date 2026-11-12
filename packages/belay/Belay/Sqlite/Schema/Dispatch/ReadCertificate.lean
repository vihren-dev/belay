import Belay.Sqlite.Model.Frontend.Codecs.Codec
import Belay.Sqlite.Queries.Evaluation.ReadCertificate

set_option doc.verso true

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
structure ReadCertificate.Obligations (certificate : ReadCertificate) (context : ResolveContext)
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

end Belay.Sqlite
