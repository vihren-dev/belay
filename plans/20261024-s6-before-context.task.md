# S6: the fixed initial database in read-only postconditions

Created 2026-10-24. Status: IN PROGRESS. The query-source/CTE/view representation is complete.
Status: [progress](20261024-s6-before-context.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S6 and its two-state guide
requirements; [S6 foundations](20261024-surface-s6-foundations.task.md).

## Purpose and boundary

The guide's postconditions compare the final database with the fixed database
at the start of the program through `before.t`. The prototype established that
the current model resolves and reads only one catalog/database. The translator
also rejects schema-qualified sources and three-part column references.
An alias alone cannot give the promised meaning.

This task adds a read-only initial/current query context to the existing model.
It supplies the model prerequisite for S6's assertions; the full triple notation
and guide proofs remain in the full S6 task. A general ATTACH implementation,
writable attached databases and a new surface SQL evaluator are outside scope.
The bounded context is an implementation choice that supplies the guide's stated
two-state observation without introducing general connection attachments.

## Required outcomes

- **Two origins have exact meanings.** The query primitive accepts explicit
  initial and current databases. A source `before.t` reads table `t` from the
  initial catalog/rows; an ordinary source reads the current database. This
  meaning does not depend on table order, matching names or equal schemas.
  The initial database is immutable for the observation. The primitive accepts
  arbitrary supplied databases; convenient assertions later fix the real start.
- **Resolution preserves origin through the whole query.** Supported aliases,
  joins, scalar/IN/EXISTS subqueries, correlations, compounds, ordinary CTEs and
  views retain each source's catalog and row origin. Three-part column names
  resolve against the intended qualified table; native SQLite has no three-part
  star, so `before.t.*` stays a syntax error. A table alias named `before`
  remains an alias in a two-part column reference; a quoted identifier containing
  a dot remains one name. CTE shadowing follows the existing scope rules.
  Expanding a view from the initial database uses that definition's original
  catalog context for its internal references, without capturing current tables.
- **Values and metadata come from the same source.** Rowids, generated-column
  values, names, declared types, affinities and collations follow the chosen
  table/view. Joins, comparison coercions, star expansion and EXCEPT use those
  exact properties. The initial and current versions of a table may have
  different column counts, order, types or names; positional coincidence must
  never mix their cells or metadata.
- **Non-database inputs retain the ordinary context.** Parameter numbering and
  values, the supplied clock and counters use the existing evaluator context.
  Reading `before.t` does not reset them to values from an earlier statement.
  The initial snapshot supplies catalog/rows, not an independent runtime clock.
  Function and pragma-source forms retain their existing admitted scope;
  extra schema-argument forms are not implied by this task and stay refused,
  as do references to `before` inside view and trigger bodies.
- **The same evaluator performs the observation.** Resolve and evaluate the
  extended query through the existing query pipeline. No concatenated untagged
  catalog, copied query interpreter or textual substitution stands in for source
  identity. Expose a small pure context/resolution/evaluation boundary that the
  later holds/Hoare-assertion layer can call without inspecting engine internals.
- **Ordinary SQL keeps its meaning.** A conservative-extension theorem relates
  the new evaluator in its ordinary one-database context to the existing query
  execution, including metadata, permitted outputs, failures and restrictions.
  A second theorem shows that a query which does not read the initial origin is
  independent of the supplied initial database, with exact binding premises.
  Existing surface programs do not silently gain a connection attachment.
  A before-qualified query used without the proof query context is explicitly
  refused at the existing supported boundary; it never reads the current table
  by fallback. Other unsupported attached-schema forms keep their restrictions.
- **Missing or unsupported data is not a successful empty observation.** Name,
  arity and scope errors use the existing error classification and source
  positions. Query failures, unavailable clocks/counters and plan-sensitive
  outcomes retain their existing meanings. A postcondition cannot prove a frame
  merely because an initial table was missing or an expression was unmodeled.
- **The surface can construct the observation without new semantics.** Provide
  the minimal checked frontend entry needed to translate/resolve a read-only
  two-state query with explicit databases. Reuse the parser, parameter planning,
  resolver diagnostics and source mapping. The normal sql/db! forms and runtime
  write paths remain governed by their current context. A full public Hoare
  notation is not required to test this model boundary.
- **S6 can fix the initial snapshot compositionally.** State the primitive's
  immutable-initial-database contract and demonstrate a modeled write followed
  by an observation of both databases. Changing the current database changes
  only current-origin reads; repeated observations keep the same initial rows.
  The full S6 task will carry that fixed value across bind and quantify over
  every permitted continuation. The accepted strong equivalence and the guide's
  explicit schema/effect premises do not change this observation primitive.

## Tests and acceptance

Kernel fixtures cover equal/different initial and current tables, absent tables,
different catalog positions and schemas, rowid aliases, generated columns,
NOCASE/BINARY and affinity differences, joins and NULL extension, correlated
subqueries, CTE shadowing, views and EXCEPT. Include the same table name in both
origins, an alias named before and a quoted name containing a dot. An unchanged
ordinary query must have unchanged outputs with several unrelated initial
databases. Exercise bound parameters, clocks, counters and error propagation.

Pinned native SQLite provides a differential observation oracle by attaching a
separate immutable copy as before. This is a test device, not a model claim of
general ATTACH support. Compare rows, metadata and errors for supported queries.
Keep the initial copy fixed across a sequence of current-database changes;
include a mutation that reads current rows for an initial source and must fail.
Reject writes/connection attachment attempts through the read-only entry point.

A Nix-selected surface fixture exercises translation, explicit context use and
source diagnostics through the installed library. It compares tables around a
concrete supported write; no unproved universal guide assumption is needed.
Audit public proofs for forbidden axioms. Every new test has a finite timeout.

Each coherent commit gets focused checks, dev-build, relevant dev-verdict and
independent review. One acceptance boundary runs post-review `just test-full`
and `just verdict`, followed by task-end `just test-nix` and
`just test-scheduled-checks`. The latter follows the owner's no-broad-local-
mutants override in [coordination](20261024-adr17-coordination.status.md).
Only Nix results are acceptance evidence. Existing frozen predictions and
mustAgree claims stay unchanged; authored oracle evidence follows the separate
judge-PR workflow if it changes a corpus/claim/lock.

## Existing interfaces and ownership

Use the completed source-reference representation, Resolution/Scope,
SourceList/SubqueryResolution/QueryForm, Resolved.EvalContext, QueryFunctions
and Subqueries. Translation/Sources and QueryExpression currently reject the
qualified forms. The source extension must retain the text package's public
codec boundary and the model's Init-only dependency rule.

Query-source/view work owns these files until its acceptance boundary. Coordinate
the integration before edits, and update existing S4 query contracts/callers
without weakening their premises. Keep origin lookup, resolved source metadata
and evaluation separate where their contracts differ; no generic multi-engine
or arbitrary attachment framework is required. Files remain below 200 lines,
with checked public docs and proof sketches. Report a demonstrated contradiction
before changing the promised two-state meaning.
