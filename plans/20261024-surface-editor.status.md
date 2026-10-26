# Status: SQL editor information and corrections

Created 2026-10-24. Status: OPEN. Part 1 and part 2a are accepted; part 2b is in progress (the model name trace is merged).
Task: [task file](20261024-surface-editor.task.md).
Specs: ADR 0017 editor features and ADR 0016 layer boundaries.

## Owner request

On 2026-10-24 the owner instructed: "continue working until adr17 is done.
after specifying a task in a task file the task should be done by a subagent."
The request also requires separate workspaces for parallel tasks, disjoint
edits and sufficient resources. The scope interpretation and review disposition
below explain why this task closes ADR17 work rather than adding a new goal.

## Evidence and constraints

The read-only editor/doc-block audit found no SQL hover/provenance registry,
name-fix emitter, trap linter or actual LSP fixture in the inspected surface.
Existing translator spans, parameter plans, resolver scope/affinity and native
Lean info/code-action APIs are the reusable inputs. No server feasibility
probe had run at specification time. The first-unit real-server Nix results
are recorded below; compiler-source inspection alone is not acceptance evidence.

The owner kept the current DQS-on/FK-off defaults. The separate private guide
correction implements that decision. Doc-block syntax and S7 formatting have
their own accepted tasks; S7 package-root ambiguity remains a separate owner
decision. This task changes none of those contracts.

## Progress

- 2026-10-24: specified observable server behavior, exact source and scope
  requirements, missing-origin behavior, bounded typo corrections, and warning
  evidence. Task review and an isolated implementation workspace are next.
  Schema integration must coordinate with the active query-source owner.
- 2026-10-24: independent review `20261024T132607Z-11cc3da1` found no musts
  and one scope-attribution should. The task now connects its required behavior
  to the owner's ADR17 completion request and the existing S2/S3 SQL forms.
- 2026-10-24: follow-up review `20261024T132710Z-9383cec2` found no musts and
  repeated the scope should. Rejected with a recorded reason: ADR17 keeps the
  guide as its target and assigns these editor behaviors to slice task design;
  it does not defer them beyond completion. These are public SQL surface
  behaviors for existing forms, not speculative support infrastructure. The
  owner's completion request therefore remains the authority for this scope.
- 2026-10-24: final task review `20261024T132927Z-4be46bc9` has no findings.
  The task still matches that reviewed revision byte for byte. Assigned its
  first acceptance part to `text_build_boundaries` in isolated
  `sqlite-verifier-surface-editor`, based on checked search/execution integration
  `3a632d10`. The same worker owns the frozen S7 parameter/source helpers and
  the checked doc-block unit, so shared interfaces can be coordinated without
  concurrent edits. Existing SQL terms, parameter semantics and source metadata
  must remain unchanged. The actual Lean server, including hover ranges and
  semantic-token responses, supplies required first-part evidence.
  Schema/origin/correction/warning behavior remains in the second part and needs
  the completed query-source interfaces. The first coherent checked commit
  will await independent review after the reviewer login refresh. No editor
  implementation or acceptance result is claimed here.
- 2026-10-25: carried the exact reviewed task/status and all three review records
  in `7bd4adde`, on immutable `3a632d10987e232ccbf818ce49b1936b2758c969`.
  The four shell files match the approved doc-block workspace; standing dev-shell
  authorization applies. The other task workspaces remain frozen.
- 2026-10-25: implemented the first source/parameter unit in the isolated editor
  workspace. `SqlEditorSource` supplies an explicit byte-range map and checks
  source-byte agreement before creating original-source information.
  `SqlParameterInfo` consumes existing plan slots and translator numbers; it adds
  native term/hover information without another numbering rule. `SqlTerm` retains
  each captured expression before coercion, uses its coerced value in the original
  script construction, and leaves source/replay annotations intact. The changed
  `variableValue` pair return needs a mechanical adaptation when the frozen S7
  shared builder is later integrated; no old workspace was edited.

## First-unit evidence and remaining acceptance

The production source is frozen at `a075cb27a400e89cb2fafa6298e9d56ef113a450`.
The test runtime correction is in snapshot
`44b4286cd2fd710a26ce0e174102823523f0fc8c`, with identical production files.

- Focused Nix real-server checks passed: 2 passed, 89 deselected, report
  `/nix/store/8d538sd8bf49gx9qqnrd8rimpcaxbs27-sqlite-verifier-test-surface-1`.
  They run the actual pinned `lean --server`, supplying installed artifacts via
  the existing module-setup contract. LF and CRLF fixtures check exact UTF-16
  hover ranges after non-BMP text, 19 parameter occurrences, pre-coercion
  `String`/`Int64`/`Value` types, do locals and constants, generated names/numbers,
  repeated parameters and per-statement slot changes, aliases and sparse slots.
  Native definition requests identify captured binders/constants/do locals.
  Local and generated arguments receive native variable semantic tokens;
  constants retain native constant behavior. SQL keywords and uncertain escaped
  mappings receive no extra tokens.
- The earlier selected Nix run had 17 passing compatibility/layer checks and
  two failed server starts. Pinned Lean's watchdog reads the UTC zone file;
  the suite lacked timezone data in the sandbox. The corrected surface test
  derivation sets `TZDIR` to pinned `pkgs.tzdata`, without a host dependency.
  The two-case retry above is successful acceptance evidence for the server.
- The development build and local diagnostics are not acceptance evidence.
  Local compatibility exposed an independent baseline S5 regression:
  `CheckReplayData` globally registers `ToExpr Output`, so `#eval` selects Lean
  constructor printing instead of the existing custom `Repr`. A diagnostic
  control removes only that instance attribute and restores `[done 1]`.
  Root confirmed the baseline cause and assigned its repair to the S5 owner.
  Existing `GuideParameters` expectations are unchanged. Logs and the control
  are under `build/agent-logs/`.

The S5 repair is checked at source `b5f15c67` and reviewed without findings in
`20261025T001733Z-b5f15c67`; its immutable evidence head is
`025c878abedbf58927d8abe37256f15b65ac14f9`. The new merge `7a0f08fd` joins that
head with editor snapshot `31f35d225c1f332f8c1a526b9eff9cafa36a76e4`, preserving
both histories with no conflicts. The repair parent also carries the reviewed
stored-view/search integration. Five editor source/fixture files are byte-identical
to the frozen editor parent; the only changes from the repair parent are the
known editor implementation, task and review records. Both fixture registrations
are retained. The comparison record is
`build/agent-logs/editor-repair-merge-equality.json`.

The second conflict-free merge `4f65073e` joins the unchanged first merge/status
`3d803229` with accepted S5 policy/review head
`bf3fa71fec3bf604b057a17141c50a2832b7aebf`. This adds only the reviewed
`CheckClaim` policy extraction, its S5 status and three review records. Eight
editor/configuration/test files remain byte-identical to `3d803229`; the exact
comparison is in `build/agent-logs/editor-query-policy-merge-equality.json`.
Neither prior editor parent was amended.

The combined Nix check passed on snapshot `67c2e611`: 23 passed, 72 deselected
in 104.15 seconds, report
`/nix/store/pfqbwzf1dvcfbdjzhl2fyavl3fwca3dv-sqlite-verifier-test-surface-1`.
It covers both real-server newline cases, the unchanged guide parameters and
parameter diagnostics, replay, all three shared-search checks, parser behavior
and the ten layer checks. The original guide-parameter printing regression is
resolved in this combined tree. The mandatory development build passed; it is
a local diagnostic, not acceptance evidence. The sequential gate is terminal;
logs and its exact command are in `build/agent-logs/editor-combined-*`.

Root's source read found no semantic issue, but it is not independent review.
Explicit independent review `20261025T003033Z-31f35d22` covered the full
nine-file editor change: no musts and two R9 shoulds, both missing module
overviews. The two checked overview comments are added without changing any
declaration or test. Their Nix retry passed on source `748607f9`: two real-server
cases passed, 93 deselected, in 2.43 seconds; report
`/nix/store/bzy1b1fwjxlk3m36r0kbirncv3j7jrq6-sqlite-verifier-test-surface-1`.
The mandatory incremental development build passed after qualifying one module
documentation reference. Its initial short-name error and final log remain local
diagnostics. Both R9 findings are recorded fixed in `f40b07c5`; its independent
review `20261025T003305Z-f40b07c5` completed with no findings.
The 23-case result above remains the compatibility evidence for unchanged code.
Integration review `20261025T003132Z-495d7693` completed with no findings.
Neither prior editor parent was amended.
First-part full/verdict acceptance follows its independent review. Schema facts,
table origins, corrections and warnings remain in the second part, together
with completed query-source integration. The overall task remains OPEN.

## Checked-command and editor integration — 2026-10-25

Merge the accepted S5 part-2 head
`eb0391448b3b2b99932e27b21948cbd56c1c53e0` with reviewed editor head
`8ca6d7ae48c6e7199e1c32f81ee3a2dd69fa4f81`, without conflicts or source
resolutions. The frozen test source is
`cc0370208bb1b999f5e57fdaa5587ad379e33b09`. Both fixture registrations,
Lake roots and the pinned timezone input are retained. The editor source and
server fixtures match their reviewed parent; model, text, conformance and
protected evidence inputs match the S5 parent. Exact comparison is retained in
`build/agent-logs/frontend-editor-source-equality.json`.

The focused Nix gate (session `97270`) passed 27 checks, with 77 deselected,
in 427.63 seconds, at
`/nix/store/w66zvq6g5kgmvziijdzwj8svfygvwzxv-sqlite-verifier-test-check-editor-1`.
It covers both actual-server newline cases, checked commands and tactics,
nondefault sampling options, all three shared-search fixtures, explicit witness
certification, replay, unchanged guide-parameter output and layer boundaries.
The merge is ready for independent review. Editor part-1 full/verdict acceptance
remains pending; the focused gate does not replace it. S5 part 2 remains accepted,
and automatic checking remains open. The source is frozen while review runs.

Independent merge review `20261025T021502Z-e8213565` completed with no findings
for `e8213565be9555d9f551c5f08b972882c66ca6ba`. The focused Nix result above
was checked directly from its immutable report; the reviewer did not rerun it.
The editor part-1 full/verdict gate remains queued. Automatic work is isolated
in a separate workspace on this immutable merge, so it cannot change that gate's
source.

## Editor part-1 acceptance on the checked-command integration — 2026-10-25

The post-review sequence on frozen
`735d2b33110e84d4a613a3dc729f52325d66ef80` (session `5008`) completed with
exit zero. Automatic-checking drafts live in a separate workspace and are absent
from these inputs.

- `just test-full`: 967 Nix tests passed, with zero failures, errors or skips,
  at `/nix/store/60g332p4mqcsklyhkpdr9q27z666i648-sqlite-verifier-test-reports`.
  The surface suite passed 104 checks at
  `/nix/store/wwb4wrlbf17j4i6xfakkxnfxg9c35clx-sqlite-verifier-test-surface-1`.
- `just verdict`: all frozen claims pass at
  `/nix/store/gldj7zm5hv9zah0jjif51dqzsdzyrhy3-sqlite-verifier-verdict`.
- All 53 prediction files and 7,372 cases remain byte-identical to the accepted
  stored-view baseline. The output is
  `/nix/store/1n22b69h6f0df7l9hzpydw7biwhx3pna-sqlite-verifier-predictions`.
  Exact comparison and JUnit totals are retained in
  `build/frontend-editor-comparison.json` and
  `build/frontend-editor-full-summary.json`.

Editor part 1 is accepted. Its schema metadata, origins, corrections and warnings
remain open in part 2. S5 parts 1 and 2 remain accepted; automatic checking and
regression actions remain open in S5 part 3. Neither whole task is complete.

## Automatic editor actions — 2026-10-25

The automatic editor tests (six action shapes, local option controls and two
document-edit cancellation cases) passed in the focused Nix gate
`/nix/store/11rz63050cnrdwl6wpkk2fdc6jib0q7x-sqlite-verifier-test-automatic-1`
(54 passed, 70 deselected). See the S5 status file for the cancellation limit.
Editor part 2 remains open.

## Part 2 split — 2026-10-25

The R19 check of the task against the current model found that no resolver
output says which name occurrence resolved to which catalog object: resolved
statements hold catalog positions, prepare errors hold only a name, and
`Span.leaves` is not a role trace. A surface-side walk would be a second
resolver over the rewritten CTE and view copies. The coordinator decided that a
model-side name trace becomes its own model task. The task file now states the
trace and splits part 2 into part 2a (table-level behavior, no trace) and part
2b (column, affinity, correction and DQS behavior, which consumes the trace).
Part 2a progress is recorded below, one entry per commit.

### Part 2a, commit 1: table hovers in `sql!` — 2026-10-25

- New modules (all in `packages/belay/Belay/Sqlite/`, each under 200 lines):
  `SqlTableSlots` (table-name places by fixed syntax path, checked against the
  name that the syntax holds, `WITH`-defined names excluded), `SqlStatementContexts`
  (catalog and row knowledge per statement: rows known until the first statement
  that can write), `SqlTableDescription` (hover text), `SqlTableInfo` (the Lean
  info tree node: hover, optional definition target, `property` token) and
  `SqlEditorInfo` (the shared entry point `emitSqlEditorInfo`).
- `SqlBang` calls the entry point after it logs the resolution errors. Plain `sql`
  has no database and so no table information.
- Finding on semantic tokens: Lean derives tokens from term information only for
  local variables (`variable`) and for the field of a projection (`property`,
  syntax kind `identProjKind`). A table name uses the `property` token through
  that node kind. There is no token type for tables.
- Tests: `tests/surface_editor_tables_test.py` (real server, LF and CRLF:
  hover text and range, row counts before and after a write, `CREATE`/`DROP`
  sequence, quoted names, CTE shadowing with no information, plain `sql` and an
  escaped literal with no information, `property` token, UTF-16 ranges after a
  non-BMP character). The helpers `position`, `hover` and `semantic_tokens` moved
  to `tests/lean_server_support.py`. The test is in the `surface` suite of
  `tests/nix_suites.json`. Nix results follow at the end of part 2a.

### Part 2a, refactor after review 1 — 2026-10-25

The review of commit 1 gave two musts, both fixed. `tableSlotsOf` now lists every
statement form, so a new form fails to compile instead of getting no information.
`mayChangeRows` now counts every statement that creates, drops or alters a catalog
object, because a dropped view or index moves the catalog positions that index the
stored rows; the test adds a view dropped before a populated table.

### Part 2a, commit 2: table origins and navigation — 2026-10-25

- `SqlTableOrigins` holds the surface environment extension `tableOriginsExtension`:
  one entry for each declaration whose value is a `db!` term, with the folded
  table name and the source range of the table name in its last `CREATE TABLE`.
  The entry is outside the database value and the script value. `db!` records it
  (`registerTableOrigins`) for the declaration it elaborates in (`getDeclName?`),
  only for tables of the final catalog, and none for a script with `ROLLBACK`.
- `sql!` reads it through `KnownDatabase.ofTerm`: the elaborated database term
  must be a constant, or constants that stand for each other, whose value holds
  the recorded literal. A computed database (`id db`) has no origin and no jump.
  `emitSqlEditorInfo` drops the origin for a name that an earlier statement of the
  script created or dropped. `evaluateDatabase` now returns the term with the
  value (`EvaluatedDatabase`).
- Finding: the recorded proof argument of the `db!` term does not survive
  `def` elaboration (Lean abstracts nested proofs), so the match compares the
  database literal only.
- Alternative kept for the report: `db!` already marks its term with `withSource`
  metadata; the task asks for an extension, so navigation does not use it.
- Test: `tests/surface_editor_origins_test.py` (real server, definition requests):
  two databases with an `items` table keep distinct origins, a constant that
  names another database, a helper module compiled to an `.olean` and imported,
  the last `CREATE` after a `DROP` inside a `db!` text, no jump for a computed
  database, no jump after `DROP`/`CREATE` inside a `sql!` script, owner in the hover.
  `tests/surface_support.py` and `tests/lean_server_support.py` got the module
  name, the helper-module compile and `LEAN_SRC_PATH` for it. Nix results follow
  at the end of part 2a.

### Part 2a, refactor after review 2 — 2026-10-25

Two musts fixed: the origin recorder lists every statement form (`isRollback`,
`stepCreatedSlots`), and the alias chain limit is the named `aliasChainLimit`.
The table-hover test expects the owner now shown in the hover (commit 2 added it).

### Part 2a, commit 3: rows of a run in `db!` and `#sql` — 2026-10-25

- `db!` runs its statements again with `executedContexts` after the run that
  finds the errors, and gives its table names the rows that the run reached before
  each statement. The second run is the same deterministic model run, so no
  second definition of execution exists.
- `#sql` is now a command elaborator, not a macro. It evaluates the database term
  and runs the script in a trial (`sqlCommandInformation`) whose messages and
  information it drops, so Lean shows each error once, at the `#eval` of
  `Database.tables` that it still elaborates. The trial keeps nothing when the
  database has no value or the text has an error. Then it emits the table
  information with the actual rows.
- Test: `tests/surface_editor_executed_test.py` (real server): counts before and
  after an insert and a delete in `db!` and `#sql`, an unrun `sql!` after a write with no count, and
  only information messages. `table_hover` moved to `tests/lean_server_support.py`.

### Part 2a, refactor after review 3 — 2026-10-25

Must fixed: the `#sql` trial does not know the values that the displayed run binds
to the parameters of a script. A script with a parameter now gets the contexts of a
resolution, whose rows are known only before the first statement that can write, instead
of the contexts of a run. The executed test adds a `#sql` with a captured `$target`.

### Part 2a, commit 4: order warnings — 2026-10-25

- `SqlOrderWarnings` (option `sql.orderWarnings`, default true). Contexts:
  - `db!` and `#sql` run their statements, so they give the evidence warning: a
    statement whose output is `Output.oneOf` (several permitted results) warns at
    the statement with the number of results and, for `LIMIT`/`OFFSET`, that
    dependence. A single or equal result gives none (`Output.ofResults` already
    merges equal results).
  - `sql` and `sql!` do not run, so they give only the risk warning: a query with
    `LIMIT`/`OFFSET`, no `ORDER BY` and a source of rows or a compound. It says the
    selection may depend on the order and that the results may be equal. Known
    limit: a one-row aggregate with `LIMIT` also gets it; the option turns it off.
  - A `#sql` script with parameters gives the risk warning, because its trial run
    binds no values. The `#eval` that `#sql` expands to elaborates with the
    option off, so a statement warns once.
- Warnings never change the term, success or proof obligations; the test checks
  that no diagnostic is an error.
- Existing fixtures: three `#guard_msgs` commands in `tests/surface/` that show
  the unordered `LIMIT` idiom on purpose now say `set_option sql.orderWarnings
  false in`. The private guide's examples of this idiom need the same line, or
  their expected messages need the warning (guide change for the coordinator).
- Test: `tests/surface_editor_order_test.py` (real server): evidence in `db!` and
  `#sql`, equal and single results and `ORDER BY` with none, risk in `sql!` after
  a write and in plain `sql`, no source with none.

The source-position test (`test_source_positions_and_failures`) adds an ordinary
literal without escapes, a multi-line raw literal with repeated occurrences, a
literal with an escape (no information), text that the parser rejects (only the
existing error), and the check that a keyword gets no semantic token.

### Part 2a, Nix results — 2026-10-25

After the final review of the part (no findings on the last commit) at
`db34f58e`:

- `just test-full` passed. The surface group, with the four new editor test
  files and the changed guide fixtures, is
  `/nix/store/yn5lyy6qhyv2bv823hdyzcpf3vl3wjcc-sqlite-verifier-test-surface-1`
  (146 passed). The source-check group had 469 passed. The conformance runtime is
  `/nix/store/qx367sqwhxgwcxp1hz7qplns2gb6rmv7-sqlite-verifier-conformance`, the
  public documentation `/nix/store/xvs1d5nniq5c7dvgpgcak85jmvzbkbrl-sqlite-verifier-public-documentation-1`
  and the report `/nix/store/96crr0c22qhwqn1q5rl0mzv1nw4384s6-sqlite-verifier-test-reports`.
- `just verdict` passed:
  `/nix/store/ndsqyfmx2i16r6ikj8r6aad55rgn8jvn-sqlite-verifier-verdict`. Part 2a
  changed no model file, no judge file and no prediction input.
- `just test-nix` and `just test-scheduled-checks` run at the end of the whole task, after part 2b.

Part 2a is complete. Part 2b (column and affinity hovers, derived-column facts,
typo corrections, DQS warnings) waits for the model name trace.

### Coordinator decisions on part 2a — 2026-10-25

Part 2a is accepted. The coordinator decided:

1. Navigation keeps the environment extension (`db!` source metadata is not used).
2. `db!` keeps the second model run (`executedContexts`) after the run that finds errors.
3. The syntactic risk warning also applies to one-row aggregates with `LIMIT`;
   `sql.orderWarnings` turns it off.
4. `sql!` keeps the risk warning only; it gives no evidence warning.

Part 2b waits for the model name-trace task. The coordinator integrates part 2a
into the stack after the FK pull requests and runs the gates on that merge.

### Integration gates — 2026-10-25

The merge `99713acb` joins part 2a with the stack head (S7, doc blocks, FK part 2).
Resolutions: the order-risk warning is in the inline `scriptTerm` of `SqlTerm.lean`
(`sql_file` and `sql_module` give no risk warning, which the task does not ask for);
`EvaluatedDatabase.value` is used by `sql_file` and `sql_module`. These two paths
record no table origins or hovers; the task scopes part 2a to `sql!`, `db!` and `#sql`.
The review of the merge found two items, both documentation: the parameterized-script
exception of `#sql` in the task file, and the acceptance line in the opening status.

Gate results on the merge `99713acb` plus the documentation refactor (2026-10-25).
All gates ran through `heavy.sh` and passed on the first run:

- `just test-full`: 337 tests passed;
  `/nix/store/djshh9r2jv947vhhi51q38mdl2jrvvjb-sqlite-verifier-test-reports`.
- `just verdict`: `/nix/store/a6nvwbx7sb8lx6fwjpr28g512dx1awxz-sqlite-verifier-verdict`.
- Predictions: the store path is `/nix/store/2c56akphxc884accaa9piqwgyhg3bpbq-sqlite-verifier-predictions`,
  the same path as the predictions of the v54 pull request, so the content is identical
  (55 files; `diff -r` shows no difference).
- `just test-nix`: 71 tests passed.
- `just test-scheduled-checks`:
  `/nix/store/3i7hzkw8i92k129kab7kjr8rhabbzlfb-sqlite-verifier-scheduled-check-reports`.
- `just review`: the merge `99713acb` had two findings (task-file documentation), both fixed;
  the refactor commit `798c25b3` has no findings.

## Part 2b — 2026-10-26

Base: the merged model name trace (`4fc773a5`). Task section "Part 2b coverage" states what the
trace covers (spec commit `95f4dc96`; R19 check of the task against the trace: no requirement is
unreachable, the DDL-body, trigger-program, unused-WITH, star-expansion and view-body gaps of the
trace limit the coverage, and the task now says so).

### Commit 1: column and comparison hovers, corrections, DQS warnings

Files (all in `packages/belay/Belay/Sqlite/`): `SqlNameSites` (trace occurrences to byte ranges:
exact paths only, one place per decision, conflicting records dropped, bytes must write the name),
`SqlKeywords` (keywords that need double quotes in a correction), `SqlNameCorrections` (edit
distance 1 to 2, deterministic ties, quote style kept, all-or-nothing when a name is unsafe),
`SqlNameDescription` (hover text), `SqlNameInfo` (hover and `variable` token for a column, hover
for a comparison, DQS warning, quick fixes through `TryThis`). `SqlStatementContexts` now keeps
the `ResolveState` of each statement, `SqlEditorInfo` runs `resolveStatementTraced`, `DbBang`
emits the editor information also when `db!` fails. Decision: a name in the body of a stored view
(`exact = false`) is not described, because its use-site path is the table hover of part 2a.

Tests: `tests/surface_editor_names_test.py` (column hovers, comparison hovers, tokens and
exclusions) and `tests/surface_editor_corrections_test.py` (quick fixes, applied corrections with
non-BMP text and CRLF, DQS warning), both in the `surface` suite of `tests/nix_suites.json`.

### Refactor after review 1 — 2026-10-26

Finding R11 (must): a quoted replacement such as `"select"` ends a raw literal without `#` or
breaks an ordinary literal. `SqlEditorSource.accepts` (`SqlLiteral.replacementKeepsLiteral`) now
refuses a replacement that would end the literal, add an escape or a carriage return; the
correction list is then dropped as a whole. Tests: four literal forms and an applied quoted edit
in an `r#` literal.

### Fix: Nix surface suite input — 2026-10-26

The first `just test-full` failed to collect the two new test files in the Nix surface suite:
`tests/surface_editor_support.py` was not an input of the suite. `build-support/tests.nix` lists it
now. The names test also checks that a checked `sql!` equals `sql` by `rfl` with the editor
information active.

### Fix: fixtures that the new information changes — 2026-10-26

The second `just test-full` run found two failing surface tests before the 1500 s limit ended the
suite (exit 124, at 96%). `DbBangErrors.lean` expects the info message of the native quick fix
(`Nearest name in scope`) for the two unknown column names. `AccountSignupQueries.lean` failed
at the base commit already (`rw [resolveOperand]` makes no progress after the name trace); the
same one-line fix (`resolveOperand_arm_compare`) is in the name-trace integration workspace, so
the two copies agree and merge without a conflict. The 20 automatic-check tests, which the limit
cut, pass locally.
