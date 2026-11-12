import Belay.Sqlite.Schema.Dispatch.ReadCertificate
import Belay.Sqlite.Queries.Evaluation.ReadAnalysis

set_option doc.verso true

/-!
An untrusted dependency analysis of reads (ADR 0017, S6). The analysis looks at a resolved statement and
the width of a table. It returns a {lit}`ReadCertificate`, or says that it does not know and why. The
analysis is conservative: it certifies only a simple read of one table with a calm filter and calm scalar
columns that read below the width. It does not know a write, a join, a subquery, an aggregate, a
grouping or ordering clause, a limit, a metadata read, a read of the clock or a counter, or a call that
can fail. Its answer is trusted only through {lit}`ReadAnalysis.analyze_sound`: a certificate
must describe the statement and must be valid. An answer of "unknown" claims nothing, so no proof depends on
the reason. The obligations of a certificate stay open ({lit}`ReadCertificate.Obligations`) until the
migration gives them.
-/

namespace Belay.Sqlite
open Model

/-- For every width, context, statement, connection and resolution of the statement on the connection: if the
analysis certifies the resolved statement with a certificate, then the statement resolves on the connection
to the statement of the certificate, with some result names. In plain words, this is the first obligation of
the certificate ({name}`ReadCertificate.Obligations.resolvesOriginal`) for the connection where the analysis
looked. Proof sketch: {name}`ReadAnalysis.analyze_sound` gives the statement of the certificate. -/
theorem ReadAnalysis.resolvesOriginal {width : Nat} {context : ResolveContext} {statement : Syntax.Statement}
    {connection : Connection} {resolved : Resolved.Statement} {state : ResolveState} {certificate : ReadCertificate}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, state))
    (certified : ReadAnalysis.analyze width resolved = .certified certificate) :
    ∃ names state, resolveStatement context connection.resolveState statement =
      .ok (certificate.statement names, state) := by
  obtain ⟨-, -, names, same⟩ := ReadAnalysis.analyze_sound certified
  exact ⟨names, state, by rw [found, same]⟩

end Belay.Sqlite
