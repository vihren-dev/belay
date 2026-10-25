# Status: S7 SQL files and build freshness

Created 2026-10-24. Status: OPEN. Assigned for implementation.
Task: [task file](20261024-surface-s7-files.task.md).
Specs: ADR17 S7/D6; ADR16 surface/tool boundary.

## Decisions and evidence

On 2026-10-25 the owner accepted the explicit package-root override. The task
and ADR17 now retain automatic discovery with source-relative
`belay.sql.packageRoot`, plus the explicit-root reader. Current file access
does not change persistent package/path identity or bypass the freshness
checker. The existing same-name nested-package probe supplies the observed
ambiguity; the amendment adds end-to-end override and relocation acceptance.
Review is pending. The S7 workspace's first unit remains at rest; no override
implementation or acceptance is claimed by this decision record.

The 2026-10-24 owner decision keeps exact SQLite result-column metadata and
native Lake tracking, and corrects the guide's blanket importer-rebuild claim.
The source audit establishes available native Lake input and needs APIs.
Package-root discovery and stale-build inspection still need real fixtures.
No production file elaborator, registry or checker exists at the inspected base.

Proof-cost reporting is required S7 scope and will have a bounded collector
prototype followed by its implementation contract. Checked SQL doc blocks have
their own reviewed task. Neither is silently excluded by this task boundary.

## Progress

- 2026-10-24: specified file semantics, lexical marker behavior, source records,
  installed checker and incremental consumer acceptance. Review
  `20261024T140732Z-6d8ca3d2` had no musts and two shoulds. Added the explicit
  layer check and named the current multi-library and package-path requirements
  behind selection/relocation tests. Await follow-up review and an agent slot.
  Reserve shared helpers with editor/doc-block tasks before concurrent work.
- 2026-10-24: follow-up review `20261024T140930Z-09c30b41` is clean.
  Assigned to `text_build_boundaries` in `sqlite-verifier-s7-files`, based on
  complete execution integration `5bc323f0`. Readiness audit found no new
  specification conflict. The first unit covers shared parameter construction,
  external-source diagnostics and package-root loading. Reserve SqlTerm,
  SqlParameters, SqlSource, EvalDatabase and SqlDiagnostics for this work;
  preserve current inline behavior and S5 metadata. S5 owns Check*, Sampling*
  and ReplayScript. Editor and doc-block work remain unassigned. Source review
  at the first checked commit waits for the owner's reviewer login refresh.
