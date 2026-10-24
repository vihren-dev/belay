# Status: checked SQL documentation blocks

Created 2026-10-24. Status: OPEN. Implementation is assigned.
Task: [task file](20261024-sql-doc-blocks.task.md).
Specs: ADR17's checked SQL docstrings and ADR16 layer boundaries.

## Decisions and evidence

The owner accepted double-quoted header strings and named closed Lean values.
The private guide correction is in product PR7. The native Verso source audit
identified the raw code-block registration path and indentation-aware source
mapping. No handler registration/compilation probe has yet run.

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

Root's source read found no semantic issue, but it is not the independent review.
The required Claude review remains blocked by the already-reported expired OAuth
login. Do not retry until the login is refreshed. Freeze this checked unit before
another feature commit; the full task remains OPEN. Public handler registration,
complete convenience/explicit bindings and environment inputs, typed headers,
expected SQL failures, lexical expected-comment extraction, original source
positions and final full/verdict/Nix/scheduled acceptance remain outstanding.
