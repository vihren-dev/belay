# Model name trace: what each name of a statement resolved to

Created 2026-10-25. Status: OPEN.
Status: [progress](20261025-model-name-trace.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), the editor requirements of S1;
[editor task](20261024-surface-editor.task.md), section "Part 2a and the model
name trace", which defines what editor part 2b consumes.

## Purpose and boundary

The resolver records no fact about a name token. A resolved statement holds
catalog positions and rewritten queries, a prepare error holds only a name, and
`Span.leaves` is not a role trace. Editor part 2b (column hovers,
comparison-affinity hovers, derived-column facts, typo corrections and DQS
warnings) needs, for each name of a statement, what the model's own resolver
decided. This task gives the model that trace. The editor itself, its hovers
and its corrections remain editor part 2b; this task changes no surface file
except where the translator's spans must locate a traced name (see below).

## Required outcomes

- **A traced entry point decides the same statement.** A model function
  `resolveStatementTraced` takes the same `ResolveContext`, `ResolveState` and
  `Syntax.Statement` as `resolveStatement` and returns the pair
  `Except NodeRestriction (Resolved.Statement × ResolveState) × NameTrace`. The
  trace is returned for failure as well as for success: after a failure it
  holds the occurrences that the resolver decided up to and including the
  failing name, with that name's admissible candidates, because editor typo
  corrections need them. The law
  `(resolveStatementTraced ctx st s).1 = resolveStatement ctx st s` is a
  theorem, for success and for failure. A script-level wrapper over the
  statement list is welcome where it is cheap.
- **The trace comes from the resolver run that decides the statement.** The
  owner decided on 2026-10-26, as the editor task said from the start, that the
  resolver is threaded with the trace, so that the trace cannot disagree with
  execution by construction. The resolver functions that decide names
  (`resolveOperand` and the functions that call it, the source, subquery,
  compound and write resolvers) get a traced form, which returns the result and
  the trace of one run. The untraced function is the projection of its traced
  form: `resolveStatement`, `resolveOperand` and every other function that the
  change touches keep their names and result types and are defined by dropping
  the trace of the traced form. There is one implementation of each decision;
  the model has no second lookup rule and no second scope rule. The projection
  law (`resolveStatement` is the first component of `resolveStatementTraced`) is
  a theorem. Existing theorems keep their statements. Their proofs may be
  repaired, for example with equation lemmas that restate the old bodies of the
  projected functions; the status file counts the repairs. The editor never
  rebuilds scopes or searches for the text of a name.
- **Every name occurrence gets one record.** A `NameOccurrence` holds:
  - `path`, the occurrence's node path in the statement as written, in the
    layout of `Restriction.path`, which `Translation.Span.select` maps to a
    source range;
  - `exact`, false when the occurrence comes from a stored view body. Then
    `path` is the use site of the view, which `CommonTableCopies.originalPath`
    collapses it to. A client may describe such an occurrence but must never
    edit it. A name in a WITH definition of the statement itself is exact: the
    copy of the definition for each use maps back, through the same function, to
    the definition as written, so two uses of one definition give two records
    with the same path;
  - the role: table reference, column reference, qualifier, alias declaration,
    result-column alias or comparison site;
  - the name as written, and for an unqualified column name the quote kind that
    the syntax keeps (`Syntax.Expr.identifier` has it; double quotes matter for
    DQS). The syntax of a qualified name, a table name and an alias does not keep
    the quote kind, and this task does not extend it: for them the quote kind is
    absent and a client reads the token text from the span;
  - the result: `found`, `ambiguous` with the candidates, or `missing` with the
    admissible candidates, the in-scope names legal at that occurrence with
    their scope source. A double-quoted name that the resolver turned into a
    text literal (DQS fallback) says so and carries the same candidates;
  - for `found`: the scope source (base table, alias, derived table, CTE or
    view, its index in the scope, and the catalog position for catalog objects)
    and the bound column with declared type, affinity, collation, primary key,
    UNIQUE, foreign-key and NOT NULL membership. The base-table origin is kept
    apart from properties inferred for a derived column;
  - for a comparison: the operator's path, the affinity the resolver applied
    (`Option Affinity`, so "none" is explicit) and the collation it used.
- **Coverage is the statement's queries and expressions.** SELECT (simple and
  compound), WITH definitions, subqueries, joins, USING/NATURAL, ORDER BY and
  GROUP BY terms, and the expressions of INSERT, UPDATE, DELETE, upsert and
  RETURNING are traced, including the S6 `before.t` sources. A name the
  resolver never looks up (for example a parse-only position) is either traced
  with its role or listed as a documented gap; no silent omission. When the
  resolver stops at an error, the names after the error are not traced, because
  the resolver does not reach them; the failing name is traced with its
  candidates. The gap list says which positions are not traced at all (the
  status file keeps that list).
- **The trace is data only.** `Resolved.Statement`, every prediction file and
  the conformance claims are unchanged, and no theorem changes its statement.
  Producing the trace changes no decision of the resolver.
- **Paths locate the name itself.** For an exact occurrence, the translated
  statement's span selects the range of the name token, not a larger enclosing
  node. Where the translator gives a node no parts today, this task adds the
  parts the traced names need in `belay-sqlite-text` (narrow change, same
  layout rule).

## Tests and acceptance

Kernel examples (`#guard`/`decide` or ordinary theorems on concrete
statements) cover: an unqualified and a qualified column, an alias that shadows
a table name, a CTE that shadows a table, a column of a derived table and of a
view (`exact = false` for names inside the view body), a correlated subquery,
USING/NATURAL merged columns, an ambiguous name with its candidates, a missing
name with ranked-input candidates, a DQS fallback, a `before.t` source, and
comparison affinity for column vs. literal, NOCASE/BINARY collations, a
unary-plus operand where no affinity applies, and a CAST operand, whose
affinity is that of its type name. Include an UPDATE, a DELETE,
an upsert and a RETURNING clause.

A test over the translated SQL of the fixtures checks that each exact path
selects exactly the name's text (`Span.select` gives the token's bytes). No test
over the frozen conformance inputs checks that dropping the trace gives
`resolveStatement`: the projection law is a theorem and `resolveStatement` is
defined by it, and such a test would need a new runner hook.

All prediction files stay byte-identical: the files that
`nix-build integrity/judge.nix -A predictions` writes (55 at the base commit,
one for each corpus input) are compared with a baseline built before the first
model change, in addition to `just verdict`, which grades the claims only. The
implementation leaves the corpus, claims and judge lock unchanged. Relevant
mutants only, by name with `-k`. Each coherent commit gets focused checks,
dev-build and independent review. One acceptance part: after final review run
`just test-full` and `just verdict`, then at task end `just test-nix` and
`just test-scheduled-checks`. Only Nix results are acceptance evidence.

## Existing interfaces and tricky points

- `Resolution/Resolve.lean` holds `resolveStatement`; 88 files mention it and
  many specs `simp only [resolveStatement, ...]`, and 35 places unfold
  `resolveOperand`. The traced forms replace the bodies of these functions, so
  those proofs need repair. The cheapest repair keeps the proof and adds a
  simp set that turns the projection of a traced body back into the old
  `Except` body. More than 80 manual proof changes would be a signal to stop and
  report to the owner.
- Name lookup goes through `Scope.resolveName`, `Scope.resolveQualified`,
  `Scope.resolveSchemaQualified` and `Scope.starColumns?` in
  `Resolution/ScopeNames.lean`; comparison affinity is `comparisonAffinity` in
  `Resolution/QueryAffinity.lean`; collation choice is in `Collations.lean`;
  DQS fallback, derived columns (`DerivedColumns.lean`), merged USING names
  (`MergedNames.lean`), CTE/view expansion (`CommonTableExpansion.lean`,
  `QuerySourceExpansion.lean`, `CommonTableCopies.lean`) and subquery scopes
  (`SubqueryScopes.lean`) each decide part of the result. The resolver is large
  (167 files in `Resolution/`): the trace is threaded through the functions that
  lead from `resolveStatement` to a name decision, which are about 40 to 60
  functions. Functions that no name decision reaches (DDL, defaults, checks and
  trigger bodies) stay untraced and call the projections.
- Restrictions already carry node paths (`NodeRestriction`), so the resolver
  already knows where it is for error reporting; the trace's paths must use the
  same layout so that one `Span` serves both.
- Candidates must be the names legal at that occurrence under SQLite's scope
  rules (correlation, aggregate, ORDER BY alias rules), not every name of the
  catalog. Ranking by edit distance belongs to the editor, not the model.
- Files stay below 200 lines, with checked public docstrings. New modules are
  imported from `Belay/Sqlite/Model.lean`.
- The table-rebuild task (column rename by binding) will consume this trace, so
  it waits for this task; it owns no resolver file meanwhile.
