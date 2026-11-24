import Belay.Sqlite.Model.Frontend.Codecs.Codec
import Belay.Sqlite.Queries.Evaluation.ReadCertificate

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- One statement realizes the scan described by a read certificate on a connection.
There are result names such that, for every clock, index and parameter list, if the table
is at the certificate position then the step returns its normalized scan, keeps the
connection and permits no further execution. -/
def ReadCertificate.Scans (certificate : ReadCertificate) (context : ResolveContext)
    (statement : Syntax.Statement) (connection : Connection) : Prop :=
  ∃ names, ∀ clock index parameters table, connection.state.database.table certificate.position = some table →
    runScriptStep context clock index connection statement parameters =
      .continued (.rows (Resolved.normalForm ((certificate.query names).results
        (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table)))) connection []

/-- A migration witnesses the actual scan on each connection. The same name finds the
two tables, whose positions can differ. The second scan appends cells to each original
row and every original row is at least as wide as the certificate requires. -/
structure ReadCertificate.Obligations (certificate : ReadCertificate) (context : ResolveContext)
    (statement : Syntax.Statement) (original other : Connection) : Prop where
  /-- The original statement realizes the certificate on its starting connection. -/
  originalScan : certificate.Scans context statement original
  /-- The named tables, the other statement's actual scan, and the row relation. -/
  appended : ∃ (name : Identifier) (otherPosition : Nat) (table extended : Table)
      (extra : List Value → List Value),
    original.state.database.tableNamed name = some (certificate.position, table) ∧
    other.state.database.tableNamed name = some (otherPosition, extended) ∧
    (certificate.moved otherPosition).Scans context statement other ∧
    Resolved.sourceRows extended = (Resolved.sourceRows table).map (fun row => row ++ extra row) ∧
    ∀ row ∈ Resolved.sourceRows table, certificate.width ≤ row.length

end Belay.Sqlite
