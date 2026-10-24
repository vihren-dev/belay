# Status: checked SQL documentation blocks

Created 2026-10-24. Status: OPEN. Implementation has not started.
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
  Review is required before assignment. Existing S4/query/S6 agents currently
  occupy the available slots. Editor and S7 helper ownership must be coordinated.
