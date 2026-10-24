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
