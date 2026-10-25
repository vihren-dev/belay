# SQL editor information and corrections

Created 2026-10-24. Status: OPEN. Part 1 and part 2a are accepted; part 2b waits for the model name trace.
Status: [progress](20261024-surface-editor.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), editor features under
"Not decided here"; [ADR 0016](../docs/adr-0016-model-and-surface.md), D2/D3.
The product guide's editor requirements were inspected at
`1fa2cb081974552cacd61beea156e52066bf2af7`; this task specifies their behavior.
Base inspected: PR #240 and the current surface at `26f8ce71`.

## Purpose and boundaries

The owner's current request is to continue until ADR 0017 is done, recorded in
[this task's status](20261024-surface-editor.status.md). ADR 0017 leaves
these editor requirements to the slices whose users need them, rather than
deferring them beyond that completion. They serve the existing S2/S3 SQL forms:
users can execute parameterized SQL now, but cannot inspect its resolved names
or apply the promised typo fixes. This task closes that missing surface behavior
alongside S4/S5; it is not tooling for a hypothetical later user base.

SQL errors already have source ranges. Users also need information about the
resolved names and parameters, navigation to table definitions, and corrections
for misspelled names. These features belong to the surface elaborator. They
must use the existing SQL translator and resolver; they do not change SQL
meaning, the proof terms, or the conformance runner.

The owner kept DQS enabled and foreign keys initially disabled on 2026-10-24.
An unknown double-quoted column that resolves to TEXT therefore gets a warning,
not a fabricated SQLite error. Profile selection remains deferred.
S5 owns counterexample/proof code actions. S6 owns claim explanation. Checked
SQL doc blocks and S7 file imports are separate tasks that reuse these APIs.

## Required outcomes

- **Parameters have useful hovers.** Each occurrence of a captured `$x` shows
  the actual Lean local or constant and its type, including a local bound in
  `do`. Other parameter occurrences show their generated argument and SQLite
  parameter number. Repeated names, numbered aliases, sparse slots and the
  distinction between parameter signs use `planParameters`; no second numbering
  rule is introduced. Parameters work in plain `sql` without a known catalog.
- **Names show their resolved facts.** For a known closed database, table
  hovers show catalog metadata and a row count when the current rows are known.
  Column hovers show declared type, affinity, collation and constraints,
  including table-owned primary/unique/foreign-key membership. Comparison
  hovers show the affinity actually used by the resolver, including cases
  where no affinity applies. Derived columns distinguish inferred properties
  from a declared type or base-table origin.
- **Metadata follows the statement's scope.** Sequential schema changes affect
  later metadata. Joins, aliases, qualified names, correlated queries and the
  completed query-source/CTE/view work use their actual scopes. Rewriting an
  expression, such as BETWEEN, must not shift information onto another source
  token. Ambiguous names get no guessed binding. Plain `sql` does not invent an
  ambient database; schema-dependent information is available through known
  `sql!`, `db!` or `#sql` contexts and the later S7 `against` entry point.
  A row count describes the known state at that occurrence. A resolved prefix
  with writes but no evaluated rows must not reuse a stale initial count.
- **Table navigation has a real origin.** A table name can navigate to its
  CREATE TABLE in a direct or imported Lean database definition. Two databases
  with the same table name retain distinct origins. Preserve source information
  in a surface environment extension keyed by declaration and table, outside
  semantic database/script values. For computed databases without known origin,
  omit the jump. Carry origin only across operations whose table identity is
  established; DROP/recreate must not retain the old CREATE location.
- **Name errors offer safe corrections.** Unknown table/column errors offer
  the nearest admissible in-scope name when its case-folded edit distance is at
  most two. A unique nearest candidate gets a correction; equal-distance ties
  are listed in deterministic order without choosing one automatically.
  Ambiguity errors do not choose a binding. A code action changes only the
  erroneous identifier, preserving valid quoting, qualifiers and surrounding
  SQL. A correctly quoted occurrence elsewhere remains unchanged. No candidate
  or an unsafe source mapping means no replacement action.
- **DQS warnings describe the actual interpretation.** When the resolver uses
  an unknown double-quoted name as a text literal, warn at that occurrence and
  offer the same bounded column correction when one exists. Existing quoted
  columns, single-quoted strings, alias declarations and ambiguous names must
  not receive this warning. State the literal interpretation; do not infer
  that every predicate using such a literal is false.
- **Order warnings have evidence.** When elaboration already evaluates a
  closed query, distinct permitted results caused by unresolved LIMIT/OFFSET
  order give a warning that names that dependence. Singleton or equal results
  do not. For a query whose rows are unknown, a syntactic risk warning may say
  only that selection may depend on order; it must not claim a proved distinct
  result. Document which contexts produce each diagnostic. Warnings never
  change result selection, success, or kernel proof requirements.
- **The editor displays the information.** Hovers, definition requests and
  code actions work through the pinned Lean server, at the SQL occurrence.
  Resolved SQL names receive semantic coloring appropriate to their available
  information; SQL keywords keep the string's ordinary coloring. Confirm this
  using semantic-token responses, not the existence of an info-tree node.
  If the native API cannot express a promised behavior, report the concrete
  finding before adding a server fork or changing the specification.
- **Source positions stay accurate.** Raw literals with arbitrary `#` counts
  and ordinary literals without escapes retain exact byte-to-source mapping.
  Unicode, non-BMP characters and CRLF must work with LSP's coordinate units.
  Escaped literals keep the documented whole-literal diagnostic fallback;
  an uncertain mapping must never replace the entire literal with one name.
  Repeated occurrences each receive information. Parser-library failures keep
  their existing actionable diagnostics rather than secondary editor errors.
- **Consumers share one boundary.** Expose a small surface entry point that
  accepts located SQL, its source mapping and an optional known database/origin.
  The future file/doc-block callers can use it without a new resolver or editor
  registry. Keep source mapping, resolved facts and Lean info emission separate
  where their independent contracts help tests. Do not add a generic plugin or
  dependency-injection framework.

## Tests and acceptance

Use the existing surface test/native-library support. Add real LSP fixtures
with finite startup, request and process timeouts. Assert hover text and range,
go-to-definition location, code-action edit and relevant semantic tokens.
Apply each representative correction and re-elaborate the edited source.
Tests of pure metadata may supplement these protocol checks, not replace them.

Cover repeated and captured parameters; two same-named tables in separate
database declarations; an imported origin; missing origin; sequential CREATE,
DROP and recreate; aliases and shadowing; correlated and derived columns;
NOCASE/BINARY and unary-plus/cast comparison affinity. Include a unique typo,
a tied typo, a distant misspelling, an ambiguity and quoted identifiers.
Check DQS positives and the nonwarning cases listed above. Order fixtures
distinguish an actual alternative result, equal alternatives and unknown rows.
Raw multiline SQL, `r##` literals, non-BMP text and CRLF protect coordinates;
escaped literals protect against destructive replacement suggestions.

Compile ordinary SQL fixtures to establish that editor information does not
change their terms, parameters, diagnostics or execution. The existing layer
checks must keep Lean editor imports out of the model and conformance runtime.
No prediction, judge-claim or lock changes are planned. Frozen predictions stay
byte-identical; investigate any difference before changing the acceptance bar.

Three acceptance parts. Part 1 is accepted: source and parameter information
with actual server coverage. The remaining schema, navigation, correction and
warning behavior splits at the model name trace (next section):

- **Part 2a** needs no per-occurrence fact from the model. It covers table
  hovers and navigation, origins, row-count knowledge, order warnings, the
  shared entry point and the source-position fixtures. The next section lists
  exactly which required outcomes belong to it.
- **Part 2b** consumes the name trace: column hovers, comparison-affinity
  hovers, derived-column facts, typo corrections, DQS warnings and every
  scope-correct claim about a name below the table level.

Each coherent commit has focused checks and independent review. After final
review of each part, run `just test-full` and `just verdict`; task end also runs
`just test-nix` and `just test-scheduled-checks`. Relevant mutants only by name.
The owner's check override is recorded in
[the build-boundary status](20261024-text-build-boundaries.status.md).
Only Nix results are acceptance evidence in status files and PRs.

## Part 2a and the model name trace

The resolver records no fact about a name token: a resolved statement holds
catalog positions and rewritten queries, a prepare error holds only a name, and
`Span.leaves` is not a role trace. Part 2b therefore needs a model-side name
trace, planned as a separate model task, not an editor edit. For each name
occurrence of a statement, the trace gives:

- the syntax path of the occurrence in the statement as written, for a name
  in a query of the statement or in a `WITH` definition of the statement. A
  name in a stored view body has no path in the SQL text.
  `CommonTableCopies.originalPath` collapses such a path to the use site of the
  view, so the trace gives that occurrence the use-site provenance and a flag
  that it is not an exact path. An editor edit, such as a correction, targets
  only exact paths;
- the resolution result: found, ambiguous or missing, with the candidates;
- the scope source and column that a found name binds, with the declared
  type, affinity, collation and base-table origin separately from inferred
  properties;
- for a comparison, the affinity that the resolver used, or none.

The trace comes from the resolver run that decides the statement, so it cannot
disagree with execution. Producing it leaves every resolved statement and
prediction byte-identical. The editor never rebuilds scopes or searches for the
text of a name.

Part 2a covers the outcomes that a fixed syntax slot decides. A table
reference slot (statement target, `FROM` source or join source, in a statement
or in an indexed subquery) is located by its syntax path, checked against the
name that the syntax holds, and resolved by the model's own catalog lookup. A
name that a `WITH` definition of the statement also names gets no information.
Part 2a gives:

- table hovers with catalog metadata and, when the rows are known, a row count.
  A context that only resolves statements (`sql!`) knows the rows of its
  database only before the first statement of the script that can write; after
  one, the hover shows no count. A context that runs each statement (`db!`,
  `#sql`) knows the rows that its run reached before the statement. A `#sql`
  script with parameters is the exception: the trial run does not know the
  parameter values, so it gets the resolution rows of `sql!`;
- navigation from a table name to its `CREATE TABLE`, with the environment
  extension, distinct origins for same-named tables of different databases,
  imported origins, no origin for computed databases, and no origin for a
  table that an earlier statement of the script drops or creates;
- order warnings. A context that evaluates its statements (`db!`, `#sql`) gives
  the evidence-based warning, from a statement output with several permitted
  results. A context that does not evaluate (`sql`, `sql!`, and a `#sql` script
  with parameters) gives only the syntactic warning;
- the shared entry point, semantic tokens for resolved tables and the
  source-position fixtures.

## Current APIs and ownership constraints

Surface files: `SqlLiteral`, `SqlTerm`, `SqlParameters`, `SqlDiagnostics`,
`SqlBang`, `DbBang`, `EvalDatabase` and `SqlCommand`. The model's `Scope`,
`ScopeNames`, `QueryExprs`, `QueryAffinity` and catalog structures supply the
facts; `Translation.Located` supplies spans. Its leaves are not a complete
token-role trace, so a textual name search or blind tree zip is insufficient.

Pinned Lean 4.34.1 supplies `DelabTermInfo.mkDocString?`/`location?`, ordinary
term information for locals, declaration ranges, `TryThis` edits and bounded
edit distance. Hover lookup requires canonical source ranges; current
`textRange` synthetic diagnostic ranges are not canonical. Semantic coloring
has additional original-source term-information requirements. Verify these
specific integration points early through the actual server.

The editor owner owns its new modules, server fixtures and narrow hooks in the
surface files above. Reserve shared parameter/source helpers and manifest
entries before S5/S7/doc-block agents edit them. The query-source and stored
view work is complete (PR 255), so its interfaces are consumable. The editor
does not edit the model package; the S6 before-context task owns the query
resolver and evaluator files until it is published, and the name trace waits
for it. No model evaluation or statement dispatch is copied into the editor.
New files follow the repository's small-file and checked-public-docstring rules.
