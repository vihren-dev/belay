# ADR 0017 coordination status

Created 2026-10-24. Status: OPEN. ADR 0017 is not complete.
This record coordinates the task/status files; it adds no implementation scope.

## Standing owner instructions

Continue until ADR 0017 is complete. Specify each task before delegating its
implementation to a subagent. Parallel tasks need separate jj workspaces,
disjoint edit surfaces and enough VM resources. Integrate useful modularity
improvements. Push completed task PRs without another permission request.
Clean completed workspaces after the code is pushed, retaining any workspace
needed for an active review. `direnv allow` is authorized. Ask for owner judgment
when a specification is wrong or incomplete, with options and a recommendation.

The 2026-10-24 handoff's check override remains: relevant mutants only by `-k`,
no broad local `test-scheduled` or `test-mutants`; task-end scheduled checking
uses `test-scheduled-checks`. No garbage collection without permission. Keep
10 GiB free on `/` and `/nix/store`. Those share a smaller filesystem than the
workspace filesystem. Reserve at most two heavy build/check processes here.

## Accepted decisions

- S5 default search infers small schemas and targeted values, with explicit
  schemas and custom generators also available.
- S5 background checks are enabled by default. Only a kernel-confirmed
  counterexample is an error; measure and expose the budget.
- ADR 0022 slice 5 splits parent-schema compatibility from row-reference truth.
  Its explicit-mapping primitive and exact engine-selected convenience helper
  preserve the existing SQLite meaning, including repeated key columns.
- ADR 0019 slice 4 supports nonrecursive CTEs. Actual recursion is excluded
  regardless of spelling, and the RECURSIVE keyword remains excluded.
- Keep current DQS-on and initial-FK-off defaults. Correct the guide and enable
  enforcement explicitly before transactions in the affected examples.

These decisions are in the corresponding tasks. A later NULL-check finding is
pending below; it does not revoke the accepted split.

## Pending owner judgment

The FK tests found that the current engine's original-column NULL check is
wrong for repeated parent keys. With `p(a,b,PRIMARY KEY(a,a))`, child
`FOREIGN KEY(x,y) REFERENCES p(a,b)` and parent `(1,2)`, native SQLite rejects
child `(99,NULL)` under enforcement. When it is stored with enforcement off,
`foreign_key_check` reports a violation. The model accepts it and reports none.
The coordinator independently reproduced both native outcomes. Pinned source
`fkLookupParent` and pragma generation test selected `aiCol`/`aiCols` child
columns; here that is `x` twice. Missing targets use the original declarations.

The task explicitly required the original NULL columns and unchanged execution
semantics, so its affected branch is stopped for owner judgment. The recommended
choice is to correct the shared engine helper, add native regressions and revise
the split API's default mapping; the alternative is to leave this work blocked
and continue independent ADR 0017 work. The asynchronous question is pending.
No engine fix has been applied. The overall goal remains active.

Two further questions are pending from prerequisite audits:

- ADR 0019 D4 says INSERT SELECT computes all source rows before writing.
  Pinned SQLite 3.51.0 streams when neither a target read nor a row trigger
  requires staging (`sqlite3Insert`, `parser/upstream/sqlite3.c:137839`). With
  source values `2, 1, -9223372036854775808` and destination `x UNIQUE` already
  containing `1`, `INSERT OR FAIL INTO dest SELECT abs(x) FROM src` reports a
  unique conflict and leaves `1, 2`. Adding an AFTER INSERT trigger whose body
  is `SELECT 1` makes SQLite stage the source: it reports integer overflow and
  leaves only `1`. Both outcomes were checked with the pinned binary. The owner
  is choosing exact streaming/staging semantics (recommended) or an explicit
  restriction for the affected cases. The slice-5 specification waits for this
  decision; no execution change has been made.
- The S7 guide says whitespace/comment edits never rebuild importing modules
  because positions are absent from terms. SQLite can include that text in
  result-column names: `SELECT 1+2`, `SELECT 1 + 2`, and
  `SELECT 1/*note*/+2` give different column names. The recommendation is to
  retain SQLite metadata and ordinary Lake dependency tracking, and correct
  the blanket guarantee. The alternative is to defer S7 for a narrower cache
  design. The source/API audit continues; no implementation has started.
- Native Verso rejects the guide's single-quoted doc-block header argument
  before a SQL handler runs. The recommended correction is a double-quoted
  string, with named closed Lean values for other types. The alternative is to
  defer checked SQL blocks for an appropriate parser extension. The question
  is pending; no header-syntax implementation or guide correction was made.

## Active implementation

- `s4_part1`, workspace `sqlite-verifier-s4`: part 1 passed its full/verdict
  boundary, then rebased cleanly onto #240 at `372e6c8f`. Part 2 is active.
  Task clarification `9f6cba9b` and monad/bind laws `51a56f7e` each have clean
  independent review. Success must cover the actual raw `oneOf` continuation
  and every concrete `rows` continuation. Part-2 success laws/fixtures are in
  progress; part 3 still removes `Run.checked`. Do not treat part 1 as S4 done.
- `text_build_boundaries`, workspace `sqlite-verifier-text-build-boundaries`:
  implementation `7d9d7d06` has clean independent review. `just test-full`
  passed with report
  `/nix/store/ykfdsmryx18cplw9zrf1dy3xakqlbydj-sqlite-verifier-test-reports`;
  `just verdict` passed, and all 53 prediction files / 7,372 cases are
  byte-identical to the baseline. `just test-nix` passed 67 tests. The final
  scheduled gate passed 47 tests. Completion review is clean and branch
  `tasks/text-build-boundaries` is pushed at `2f86e45a`. PR
  [#240](https://github.com/vihren-dev/sqlite-verifier/pull/240) is open in stack
  231, based on #239. Its exact review range is `98a07bfe` to `2f86e45a`.
  Review tab 6 (`w1:t3T`) is open, with live wait session `78895`. Keep this
  workspace at rest while that review is open. Do not open a duplicate tab.
- `foreign_key_atoms`, workspace `sqlite-verifier-fk-atoms`: part 1 of
  [the FK task](20261024-foreign-key-atoms.task.md), based on `cf7aa9a6`.
  The agent owns FK atom/check/frame modules, the surface database export and
  their registration entries in the model barrel/lakefile. S4 confirmed these
  entries do not overlap its current work. It has the cached #239 prediction
  baseline `4k77z378vnagzwx5448yqz0686d58cld`. The full pragma statement law
  will reuse S4's query-output bridge after clean integration; part 1 stays
  open until that law and its acceptance checks pass.
- The prediction filter task in `sqlite-verifier-prediction-source-filter`
  is DONE, based on #240. Both completed code workspaces remain at rest.
  Implementation `accfbf78` has clean independent review. The production Nix
  identity regression passes, all 55 locked parts are unchanged, and all 53
  prediction files / 7,372 cases are byte-identical. Full validation passed:
  792 full-suite tests, 70 Nix checks and 47 scheduled checks; verdict totals
  remain 4,838 AGREE and 2,534 MODEL_UNSUPPORTED, with no errors. The task is
  DONE, final review findings resolved, and `529ff779` is pushed as
  `tasks/prediction-source-filter`. PR
  [#241](https://github.com/vihren-dev/sqlite-verifier/pull/241) is in stack 231,
  based on #240. Review tab 7 (`w1:t3V`) is open for `2f86e45a` to `529ff779`,
  with live wait session `78368`. Do not open a duplicate review.

The S4 provisional full gate passed: report
`/nix/store/japwh8n1f0chh7fz6ig44qn9dxhkm8y5-sqlite-verifier-test-reports`,
805 cases with no failures, errors or skips. Its final post-review invocation
also passed, with verdict 4,838 AGREE and 2,534 MODEL_UNSUPPORTED and all 53
predictions files byte-identical. The part-1 boundary was committed as
`a86470b8` before the authorized rebase onto #240. Registration conflicts were
resolved without restoring removed files. Part 2's full gate will cover the
integrated base; the earlier evidence remains part-1 evidence before rebase.

`s6_prerequisite_audit` now implements query-sources part 1 in
`sqlite-verifier-query-sources`, based on clean S4 part 1 `372e6c8f`.
Task carry `8a89208f` has clean review. Baseline predictions are
`/nix/store/qwfgz46d1pyd10xiypmka4kixvx38k2b-sqlite-verifier-predictions`;
baseline verdict `srv5lc3gnn1s9wzfjy1ilrzsb2ws0881` passes existing claims.
The source-execution unit is being checked; metadata/translation remain.
CTEs and views follow as later parts. Do not rebase shared S4 ancestors.

`text_build_boundaries` completed the private guide correction at `565f1974`
in `sqlite-verifier-product-profile-guide`. Nine pinned native checks passed.
The agent is isolating the task and correction onto product PR #6's published
base, excluding unrelated unpublished ancestors, before root publication.
S4's separate guide claims/proof paragraphs remain with the S4 agent.

The read-only S7 audit is complete at
`/home/codex/work/research_notes/Lean model modularity investigation/adr17_s7_audit.md`.
Its file elaborators and freshness checker can proceed without S4–S6 once the
guide correction is decided. A task must also cover the guide's `--costs`
heartbeat reporting; the checked SQL docstring-block feature needs explicit
ownership in the remaining guide audit.
The editor/doc-block audit is also complete in the same research-notes directory.
It informs [the editor task](20261024-surface-editor.task.md), now awaiting review.
Checked doc blocks still need their task after the syntax decision.

Completed workspaces `adr19s2`, `adr19s3`, `adr22s2`, `adr22s3`, `adr22s4`,
`errev` and `envfns` were checked clean, with all nonempty commits reachable
from origin bookmarks and no running process or open review in their paths.
They were forgotten and removed under the owner's pushed-workspace cleanup
instruction. The protected `s4chk` workspace and all unrelated workspaces remain.

The schema and observation helper agents of S4 have completed their reviewed
commits and returned them to S4. Their workspaces remain until pushed cleanup.
No agent may rebase a shared ancestor while another agent is editing a descendant.

## Specified work waiting for its prerequisites

- [S5](20261024-surface-s5.task.md): reviewed; waits for S4's final success and
  run semantics. Plausible v4.34.0 still needs a compatibility build under
  Lean 4.34.1. No dependency is installed yet.
- [Query sources](20261024-query-sources.task.md): review `cf7aa9a6` had no
  findings. Covers derived tables, ordinary CTEs and views, including the
  existing compound-subquery metadata restriction; part 1 is active above.
  ALTER/rebuild follows the final view representation.
- [S6 foundations prototype](20261024-surface-s6-foundations.task.md): final
  review `1cd45bae` had no findings. Uses S4's completed monad/universal execution
  interfaces to investigate WP, congruence, the before schema and footprints.
  Full S6 still needs a task after those findings and the model prerequisites.

ADR 0019 slice 5, full S6, S7 and S8 remain to be specified and implemented.
S8's application simulation and the full guide acceptance audit are required
before the ADR 0017 goal can be marked complete.
