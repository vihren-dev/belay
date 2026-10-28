# Proof refactor acceptance repair status

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Task: [restore acceptance checks](20261028-proof-refactor-ci.task.md).
Source baseline: PR 295, `e8f46dae`; production `3e2212ed`.

## Native replay diagnosis and repair

The model producer already supplies all required native artifacts. Pinned
Lake 4.34.1 expands wildcard module selections through unsorted directory
enumeration (`Lean.Util.Path.forEachModuleInDir`). Its library builder collects
native objects in that order, and the order contributes to the saved link trace.
Thus relocation between filesystems can invalidate the shared facet while each
module and native object remains current. The direct and installed local replay
orders agree; the hosted failure is the acceptance case for relocation.

The producer manifest now uses explicit names for the four former wildcard
selections. It retains all 874 modules of the `Belay.Sqlite.Model` library.
The package's other four modules are `Codec`, `Codec.Resolution`,
`Codec.SyntaxJson` and `Codec.StatementExamples`, each under `Belay.Sqlite.Model`:
878 package modules in total. Both library declarations remain.
No source, object, output trace or installed-package permission is rewritten.
The existing package replay test checks the configuration that avoids this
failure, then requires the real immutable native facets to replay. Retire the
configuration guard when the pinned Lake sorts wildcard expansion.

The installed fixture and its seven consumer test files are unchanged. The
focused Nix invocations select existing tests from `packages`, `surface` and
`surfaceS6`; their source inputs, runtime, environment and deadlines stay intact.
No test owner or permanent runner was added.

## Resolver measurements

The existing resolver test is parametrized by each mutant's edited source file.
The parameter set and each selected table come from the same unchanged `MUTANTS`
mapping. Equality with exactly one file assigns every mutant to one group, with
neither omissions nor duplication. Each measurement retains all 16 authored
cases, the original 2,000-column-case exclusion, unchanged-model agreement, and
the assertion that every mutant changes a verdict. No timeout or harness code
changes.

| Edited file | Mutants |
| --- | --- |
| `Identifier.lean` | `non_ascii_fold` |
| `Resolution/AddColumn.lean` | `constant_column_limit`, `no_too_many_columns`, `no_duplicate_column`, `no_such_table` |
| `Resolution/Definitions.lean` | `desc_rowid_alias`, `table_index_same_name`, `no_table_exists` |
| `Resolution/ResolveStatement.lean` | `rollback_keeps_catalog` |
| `Resolution/TypeAffinity.lean` | `affinity_order` |
| `SqlAdvance.lean` | `commit_without_transaction` |

## Acceptance

The new Nix model output is
`/nix/store/mfdl4l49m8lv5phl38hmyxfsgdb9gm86-belay-sqlite-model-0.1.0`.
It contains 878 Lean module artifacts and 878 native objects. Current Nix checks:

| Existing owner and selection | Result | Report under `/nix/store/` |
| --- | --- | --- |
| `packages`, all native replay checks | 3 passed, no compiled targets | `lc9hq9b2mrs3yxjh97z0pzvmgk53xlds-sqlite-verifier-test-packages-1/junit.xml` |
| `surface`, SQL files, roots, records, Lake inputs and proof-cost reports | 24 passed | `fzpdbv90f2mmf3j0pw3hh6rhs6l7w69g-sqlite-verifier-test-surface-ci-repair-1/junit.xml` |
| `surfaceS6`, SQL checker and checker-root tests | 6 passed | `p5gl3ssaaxy7gavx9vr388glwma5a6x6-sqlite-verifier-test-surfaceS6-ci-repair-1/junit.xml` |
| `mutants`, resolver file only | 6 passed; all 11 mutants killed | `ib7rp3hpzj5gils5sjaqbpnv54ax09z9-sqlite-verifier-test-mutants-ci-repair-1/junit.xml` |

These runs used `max-jobs = 1`, `cores = 3` and the hardened Nix sandbox.
The selected consumer runs use an untracked expression in
`build/ci-repair/selected.nix` that changes only the existing owner's pytest file
selection. Logs are `/tmp/proof-refactor-ci-{packages-final,consumers,resolver}.log`.
The resolver measurements took 149.913, 111.811, 104.206, 86.370, 144.235 and
86.315 seconds in the table's order, with the unchanged 300-second test limit.
The selected resolver run took 682.963 seconds in total. These measured local
Nix times do not establish hosted headroom; the hosted Linux rerun remains
required. Other development builds shared this host during the run.

Native repair `15a4bd15` received independent Claude review
`20261028T114602Z-15a4bd15`: zero must findings and one should finding. The
finding requested the model-library versus codec module-count distinction
above; it is fixed. Resolver repair `33611eda` received independent Claude review
`20261028T115235Z-33611eda`: zero must and zero should findings. Whole acceptance
remains with the coordinator. The Linux hosted result is pending and is separate
from local Nix checks. PR 295's earlier API-reference and verdict successes do
not establish acceptance of this repair.

## Hosted follow-up, 2026-10-28

The repair was pushed as PR 295 head `16ab6ad7`. Hosted Verdict run
`40702241903` passed. CI run `40702241901` passed the API-reference build,
function-mutant job and all six resolver-mutant groups. Two later measurements
failed: query-resolution mutant `no_such_column` could not compile the imported
`Resolution/OperandArms` proof, and the grouped join measurement exceeded its
300-second limit (337.49 seconds including cleanup). These are failures, not
detected mutants. The Linux check job was still running at this checkpoint.

Logs are retained at `/tmp/ci295-122864838415.log` (query) and
`/tmp/ci295-122864838065.log` (joins). Read-only diagnosis found the operand
equation imports on the classifier's path through `Resolution/QueryExprs` at
both production `3e2212ed` and repair `16ab6ad7`. The task now covers that import
boundary and bounded join measurements with unchanged semantics, mutant edits,
target mappings and deadlines. The worker assignment follows specification
review. The already-running integrated proof acceptance remains frozen.

The join measurement combines 22 mutants and 20 distinct target cases from
the existing join, USING, right-join and merged-name tables (6, 6, 4 and 6
mutants). At timeout all four workers were compiling classifier dependencies.
Source inspection supports separate measurements of those tables with the
same target mappings. Hosted timings remain to be established. The extended
task's documentation-link diagnostic passed; independent review follows.

Claude reviewed scope amendment `7b651616` with zero must and zero should
findings (`reviews/20261028T144207Z-7b651616/review.json`). The worker is assigned
the import-boundary repair and join grouping in this isolated CI workspace.
Local diagnostics may run with bounded parallelism; Nix acceptance waits for
the coordinator's currently occupied build slot. No final acceptance is claimed.

## Operand equation imports and join measurements

`Resolution/QueryExprs` now imports `OperandProjection`, the executable owner.
The equation modules remain unchanged. Their actual proof consumers import them:
`SingleSourceNameLaws` and `TableInfoLaws` import `OperandArms`;
`ExprResolutionLaws` and `ResolveReadsBelow` import `OperandArmsMore`.
All declaration bodies, theorem formulas, attributes and proof bodies are unchanged.
The classifier's source import closure contains 290 project modules instead of
292; the two excluded modules are the operand equations. This count establishes
the import boundary, not a build-time improvement.

The existing join test now has four parameters, one for each existing authored
case module and mutant table. The join, USING, right-join and merged-name tables
contain 6, 6, 4 and 6 mutants. They retain all 22 mutant identities and their
20 distinct target cases. Each measurement still records its targets natively,
requires unchanged-model agreement, and rejects every surviving mutant. Mutant
edits, target mappings, the measurement harness and all deadlines are unchanged.

Development diagnostics use `LEAN_NUM_THREADS=2`. The package build covers the
model, text, conformance and surface libraries. A temporary partition audit checks
that every mutant occurs once and that each assigned case module contains every
target. Source checks are `mutant_guards_test.py`, `docs_test.py` and
`test_lean_categories.py`. The previously uncompilable `no_such_column` mutant
is also replayed alone through the existing `measure_set`, with the 300-second
outer deadline and unchanged target. These local diagnostics are not acceptance
evidence.

Claude reviewed implementation `7da59def` with zero must and zero should findings
(`reviews/20261028T145306Z-7da59def/review.json`). Nix acceptance remains pending. The ignored expression
`build/ci-repair/operand-joins.nix` selects the existing query-resolution test from
`mutants` and the four join parameters from `tableMutants`. It preserves each
owner's inputs, runtime, environment and deadlines. The coordinator controls the
Nix slot. The full six-query and 22-join mutant results, checked documentation,
combined acceptance and subsequent hosted Linux timings remain required.
