import Belay.Sqlite.ReadCertificate

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

/-- Why the analysis does not know a statement. Each reason names one condition that the analysis
needs and the statement does not give. -/
inductive ReadAnalysis.Unknown where
  /-- The statement is not a query, for example a write, a schema change or a transaction statement. -/
  | notQuery
  /-- The query has subqueries. -/
  | hasSubqueries
  /-- The query is not a simple read of one table. It joins sources or reads a source other than a table, it
  aggregates, groups, orders, limits or removes duplicates, or it reads a cell of an outer query. -/
  | notSimpleTableRead
  /-- The filter or a result column may read a column at or beyond the width, or is an aggregate. -/
  | readsBeyondWidth
  /-- The filter or a result column calls a function that can fail, or reads the clock or a counter. -/
  | notCalm
deriving DecidableEq

/-- The answer of the analysis: a certificate, or unknown with a reason. -/
inductive ReadAnalysis.Result where
  /-- The statement has this certificate. -/
  | certified (certificate : ReadCertificate)
  /-- The analysis does not know a certificate. -/
  | unknown (reason : ReadAnalysis.Unknown)
deriving DecidableEq

/-- A decision for whether the expressions of a certificate are calm. The expressions are calm exactly
when the {name}`Resolved.Expr.Calm` of each holds, which is decidable because it is a finite check of the
expression. -/
instance (expression : Resolved.Expr) : Decidable expression.Calm :=
  decidable_of_iff (expression.any Resolved.Expr.isFallibleCall = false ∧
      expression.any Resolved.Expr.readsClockHere = false ∧
      expression.any (Resolved.Expr.readsCounterHere .changes) = false ∧
      expression.any (Resolved.Expr.readsCounterHere .totalChanges) = false ∧
      expression.any (Resolved.Expr.readsCounterHere .lastInsertRowid) = false)
    ⟨fun ⟨fallible, clock, changes, total, last⟩ =>
      ⟨fallible, clock, fun kind => by cases kind <;> assumption⟩,
     fun ⟨fallible, clock, counters⟩ => ⟨fallible, clock, counters _, counters _, counters _⟩⟩

/-- The analysis of one resolved statement against a width. In plain words: a query without subqueries
over a single table source, which is equal to the simple query of the table with its own filter, columns
and names, is certified when the filter and columns read below the width and are calm. Every other
statement is unknown, with the first reason that applies. -/
def ReadAnalysis.analyze (width : Nat) : Resolved.Statement → ReadAnalysis.Result
  | .query query [] =>
    match query.sources with
    | [source] =>
      match source.source with
      | .table position =>
        let certificate : ReadCertificate := { position, width, filter := query.filter, columns := query.columns }
        if query = certificate.query query.names then
          if (∀ condition ∈ certificate.filter, condition.readsBelow width = true) ∧
              ∀ column ∈ certificate.columns, column.readsBelow width = true then
            if ∀ expression ∈ certificate.filter.toList ++ certificate.columns.flatMap Resolved.Output.scalars,
                expression.Calm then .certified certificate
            else .unknown .notCalm
          else .unknown .readsBeyondWidth
        else .unknown .notSimpleTableRead
      | .initialTable _ | .each .. | .subquery .. | .pragma _ => .unknown .notSimpleTableRead
    | [] | _ :: _ :: _ => .unknown .notSimpleTableRead
  | .query _ (_ :: _) => .unknown .hasSubqueries
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .drop .. | .begin
  | .commit | .rollback | .insert .. | .insertSelect .. | .update .. | .upsert .. | .delete .. | .prepareError _
  | .setting .. =>
    .unknown .notQuery

/-- For every width and resolved statement: if the analysis certifies the statement with a certificate, then
the certificate is valid, its width is the given width, and the statement is the statement of the certificate
with some result names. In plain words, a certificate that the analysis returns describes the statement it
analyzed. The theorem requires nothing of an answer "unknown". Proof sketch: unfold the analysis and split
on its tests; the equality test gives the statement and the other tests give the three parts of validity. -/
theorem ReadAnalysis.analyze_sound {width : Nat} {statement : Resolved.Statement} {certificate : ReadCertificate}
    (certified : ReadAnalysis.analyze width statement = .certified certificate) :
    certificate.Valid ∧ certificate.width = width ∧ ∃ names, statement = certificate.statement names := by
  unfold ReadAnalysis.analyze at certified
  split at certified
  all_goals first | cases certified | skip
  split at certified
  all_goals first | cases certified | skip
  split at certified
  all_goals first | cases certified | skip
  dsimp only at certified
  split at certified
  all_goals first | cases certified | skip
  rename_i query _ _ _ _ _ _ same
  split at certified
  all_goals first | cases certified | skip
  rename_i below
  split at certified
  all_goals first | cases certified | skip
  rename_i calm
  exact ⟨⟨below.1, below.2, calm⟩, rfl, query.names, by simp only [ReadCertificate.statement]; rw [← same]⟩

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
