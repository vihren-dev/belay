# Status: checked SQL documentation blocks

Created 2026-10-24. Status: DONE (2026-10-25).
Task: [task file](20261024-sql-doc-blocks.task.md).
Specs: ADR17's checked SQL docstrings and ADR16 layer boundaries.

## Decisions and evidence

The owner accepted double-quoted header strings and named closed Lean values.
The private guide correction is in product PR7. The native Verso source audit
identified the raw code-block registration path and indentation-aware source
mapping. The first-unit native registration/compilation probe now passes; the
public handler remains outstanding.

The task defines the previously unspecified output/comment/error protocol and
an explicit binding/expectation escape from convenience syntax. These are task
design choices over the accepted surface; no SQLite meaning is changed.

## Progress

- 2026-10-24: specified outcomes, compiler/rendering checks and source ownership.
  Review `20261024T135930Z-efc1f0b6` had no musts and two shoulds. Recorded the
  S7 task allocation and guide correction, and named the current parameter,
  clock and observation examples that need explicit inputs. Follow-up review
  is required before assignment. Existing S4/query/S6 agents occupy the slots.
  Editor and S7 helper ownership must be coordinated.
- 2026-10-24: follow-up review `20261024T140400Z-04f1c91e` has no findings.
  The task still matches that reviewed revision byte for byte. Assigned to
  `text_build_boundaries` in isolated `sqlite-verifier-sql-doc-blocks`, based
  on complete execution/native source `5bc323f0`. The same worker owns the
  frozen S7 helper changes, so their interfaces can be coordinated without
  concurrent edits. S7 package-root ambiguity remains a separate owner decision.
  Begin with new doc-block modules and fixtures; coordinate any shared helper
  edits explicitly. Keep the full task open until its public registration,
  binding, output, failure and source-location contracts all pass acceptance.
  The first checked implementation commit will await independent review after
  the reviewer's login refresh. No implementation result is claimed here.
- 2026-10-24: carried the reviewed task and review records on immutable
  `5bc323f056a99c6c0a9ff4ff2752baafb3d559ad` in `dbf49320`. Added only ADR17's
  accepted doc-block allocation sentence and task link. The four shell files
  match the approved S7 workspace; the standing dev-shell authorization applies.
- 2026-10-24: the first implementation unit supplies `SqlDocObservation` and
  `SqlDocCheck`. The pure checker accepts explicit text or complete typed output
  expectations. It preserves cell whitespace and every permitted alternative,
  and rejects errors, restrictions and caller-supplied empty alternative lists.
  The actual-run adapter calls the existing `Database.run`; it adds no interpreter.
  The fixture-only `sql_probe` native raw expander imports the adapter, evaluates
  a closed database through `EvalDatabase`, and retains the original body as
  documentation data. The probe's small header is an integration check, not
  the public `sql` handler or completion of the task's header protocol.

## First-unit checks and review boundary

Nix acceptance for source snapshot
`dbdfd32367f748101b6d68f3259d681154cf7f75b`:

- `project.tests.surface.overrideAttrs` with
  `PYTEST_ADDOPTS = "-k 'surface_sql_docs or surface_layers'"` passed 12 tests,
  with 76 deselected. Report:
  `/nix/store/hf7dvfi8gzkgl71g1v930im6i4xk2dmn-sqlite-verifier-test-surface-1`.
- `SqlDocObservation.lean` checks row/statement order, empty results, write
  counts, NULL versus text, BLOB/invalid UTF-8, whitespace and embedded newlines,
  typed distinctions, equal/distinct alternatives, empty alternatives, error
  classification, actual bindings, independent database runs and explicit clocks.
- The imported raw-registration probe checks preserved documentation data,
  independent blocks and rejection after either expected text or a SQL predicate
  changes. Ten layer checks retain the package boundary.

The first Nix invocation was canceled before testing because its argument list
would also have selected the rest of the surface suite. Its terminal status was
130; the corrected selected invocation above is the acceptance evidence.
Development-build and local fixture logs are diagnostics only. Logs and the exact
selected command are under `build/agent-logs/sql-docs-*`. All processes are terminal
and the heavy slot is released. Model/text sources and the judge lock are unchanged.

Root's source read found no semantic issue. After reviewer access was restored,
independent review `20261025T001749Z-3bb4171e` of source commit
`3bb4171e6e43fcf8e2af159e805c83bac3901ed1` completed with no musts and one should.
Finding `#1` (R10) requests actionable next steps in three failure messages.
The coordinator approved the narrow R10 correction. The three messages now
name a recovery action for the existing checker API, without advertising the
unfinished public failure mode. The message/docstring-only correction passed
its focused Nix check on pre-commit snapshot `04b44c5a` of change `zrqsoqno`
(the same production files committed as `10216365`): 2 passed, 86 deselected,
in 5.01 seconds; report
`/nix/store/8arqjd5l5jlnvg5v148gimnk0gbijzrp-sqlite-verifier-test-surface-1`.
The mandatory development build also passed; it is diagnostic evidence only.
No execution or expectation logic changed. Finding `#1` is recorded fixed, and
independent review `20261025T003533Z-10216365` found no musts and one R19
status-only should. The status now identifies the pre-commit snapshot explicitly;
that finding is recorded fixed. Logs and exact command are under
`build/agent-logs/sql-docs-r10-*`. The full task remains OPEN. Public handler registration,
complete convenience/explicit bindings and environment inputs, typed headers,
expected SQL failures, lexical expected-comment extraction, original source
positions and final full/verdict/Nix/scheduled acceptance remain outstanding.

## Public `sql` handler

2026-10-25 R19 check of the task against the current code: it matches. `failureDiagnostic`
binds no values or clock, `planParameters` and `Script.withValues` exist, and the native
raw-expander path is the one the first unit used. No owner decision is needed. The S7
`ParameterMode` is not needed: a doc block treats `$name` like every other name, because it takes
the value from the header argument and never from a binder.

The public `sql` block is now registered by `import Belay` (`Belay/Sqlite.lean` imports
`SqlDocBlock`). New modules, each under 200 lines: `SqlDocComments` (lexical expected-text reader),
`SqlDocSource` (map from the de-indented body to original file positions), `SqlDocBindings`
(convenience and explicit binding plans and their problems), `SqlDocHeader`, `SqlDocClosed`
(closed values by evaluation), `SqlDocInputs`, `SqlDocFailure`, `SqlDocReport`, `SqlDocBlock`
(expander and registration) and `SqlDocGuide` (checked examples, documentation only). The shared
`DbDiagnostics` edit splits `failureDiagnostic` into `failureParts`, which takes the clock and the
bound values, and a `failureDiagnostic` with the old behavior for `db!`. The fixture-only
`sql_probe` expander and its test are deleted.

Decisions inside the task. Header options are `db`, `env`, `values`, `expected` and the flag
`+error`. A convenience argument binds the parameter of its name (`?` and `?N` give `pN`); two
signs with one name (`:x`, `@x`) are an error that names the explicit list, which is exact. The
explicit list needs one list per statement and exactly the largest parameter number of values
for each. `+error` compares the message that the model gives for the failure, without the action text of
`failureAction`. For most failures this is SQLite's message. Three existing limits of the model
mean that it is the model's own text: a syntax error (the parser library reports an offset and no
message), a function failure, and a constraint failure in a write that can fire a trigger or that
checks foreign keys (`triggerOrKeyConstraintMessage`). The expected lines of such a block repeat
that text. This is not a change of SQLite behavior; a model change that gives the SQLite message
would make these blocks stricter and is outside this task. `SqlDocGuide` states the limit.
A block with a wrong header is not run, so a header error adds no second error.

Fixtures: `tests/surface/SqlDocCases{Text,Typed,Bindings,Explicit,Failures,Comments}.lean` hold 67 cases with
stated error positions. The tests elaborate each fixture with Unix and with Windows line ends.
`tests/surface_sql_doc_blocks_test.py` also mutates a passing case and checks the missing parser
library. `tests/surface_sql_docs_test.py` runs the `#guard` fixtures of the pure helpers.

Nix acceptance for source snapshot of change `wqtnqpwy` (committed below): the focused surface
check with `-k 'surface_sql_doc or surface_layers'` passed 154 tests with 76 deselected in
19.38 seconds. Report:
`/nix/store/2a6bv6p69pkyq661sfr3gijrkp9m3aj1-sqlite-verifier-test-surface-1`. Logs and the
command are under `build/agent-logs/docblocks-*`. No guide change is known.

Review `20261025T093205Z-be8ff7ba` of `be8ff7ba` found 4 musts and 3 shoulds, all fixed in the
following refactor commit: `explainStop` names every `Output` constructor; the error-mismatch and
closed-evaluation messages give a recovery action; the six case fixtures are all under 200 lines
(the old Output and Inputs fixtures are split into Text, Typed, Bindings and Explicit) and their
setup definitions have docstrings; and the limits of `+error` messages (syntax, function and
trigger or foreign-key constraint failures give the model's text) are stated above and in
`SqlDocGuide`. Focused Nix check of that refactor snapshot (`-k 'surface_sql_doc or
surface_layers'`): 154 passed, 76 deselected, 22.70 seconds; report
`/nix/store/2c3j895qgphqdbfmdqqvbw3i89kgjg4s-sqlite-verifier-test-surface-1`.

## Acceptance

Review `20261025T093900Z-5d6de3ca` of the refactor commit `5d6de3ca` found nothing. On that source
(the later commits change only status and review records), the Nix gates passed:

- `just test-full`: `/nix/store/yw7nj4f2b7xkbx3cyyafl0cagxpv47in-sqlite-verifier-test-reports`
  (its log summaries show 472 and 230 passed).
- `just verdict`: `/nix/store/fdyxvw89hvk8i7sa232c6is81sczb24d-sqlite-verifier-verdict`.
- `just test-nix`: 71 passed, 1641 deselected.
- `just test-scheduled-checks`:
  `/nix/store/j37adzg25s32slqy03advda9hfd02dwx-sqlite-verifier-scheduled-check-reports`.

Logs are `build/agent-logs/docblocks-*`. The judge lock and the frozen predictions are unchanged.
The task is DONE. By the owner's rule for this work the mutant suites are not run locally
(`just test-scheduled` and `just test-mutants` were not run; CI runs them daily), so the scheduled
gate here is `just test-scheduled-checks`. No mutant test touches the files of this task.
Outstanding outside this task: the private guide needs one correction. Its text about `+error`
messages should say what `SqlDocGuide` says: syntax, function and trigger or foreign-key
constraint failures give the model's own text, and the expected lines repeat it.

## Integration with S7 and S5

2026-10-25: merge of `00fba7b1` (this line) and `77c17f02` (S7 and S5 head), with no rebase.
Conflicts and resolutions:

- `packages/belay/lakefile.lean`: kept the S7 and S5 glob arrays and appended a separate
  `++ #[...]` array with the doc-block modules.
- `packages/belay/Belay/Sqlite.lean`: kept the S5 imports and added `SqlDocBlock`.
- `tests/nix_suites.json`: kept both lists of surface tests.
- `docs/adr-0017-user-surface.md`: took the S7 and S5 text, which already names the doc blocks.
- `plans/20261024-sql-doc-blocks.{task,status}.md`: both lines added these files from the same
  reviewed original; took this line's versions, which contain the later work.
- `DbDiagnostics.lean`, `build-support/tests.nix` and `packages/belay/README.md` merged without
  a conflict. `tests.nix` is unchanged from the S7 and S5 head. The README has a new short
  section on the doc blocks.

One semantic change follows the S7 helper: S7 gave `planParameters` a `ParameterMode`. The doc
block uses `.file`, so `$name` is an explicit argument that never reads a Lean variable, which
is the task's rule. The earlier decision that no `SqlParameters` change is needed still holds.
No S7 SQL-file module and no S5 editor or automatic-check module uses the diagnostics or the
parser entry that this line changed.

Checks of the merge: `just dev-build`, `lake build` and `lake build belay-sql-check` pass (local,
diagnostic). The whole Nix surface suite passed 300 tests in 1031 seconds, report
`/nix/store/l0g82jvd1i3sdvqqbqj4pwrkr35gp0h7-sqlite-verifier-test-surface-1`.
