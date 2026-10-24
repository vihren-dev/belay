# Status: S7 SQL files and build freshness

Created 2026-10-24. Status: OPEN. Assigned for implementation.
Task: [task file](20261024-surface-s7-files.task.md).
Specs: ADR17 S7/D6; ADR16 surface/tool boundary.

## Decisions and evidence

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
- 2026-10-24: first-unit source is at rest after shared inline/file parameter
  planning, one script constructor, external UTF-8/CRLF diagnostics and
  manifest-based package discovery. No public file syntax is exposed before
  migration-section safety is implemented. The package ID comes from Lean's
  setup; manifest dependency paths also support renamed dependencies. The
  ordinary consumer fixture uses real package directories with linked installed
  entries and the producer's pinned parser-library environment.
  Focused Nix run 1 passed 20 parameter, replay, diagnostic and layer cases;
  its consumer case failed before elaboration because of the fixture's package
  symlink layout. Retry 2 exposed the fixture's omitted parser-library variable;
  retry 3 corrected an environment-expression type error before building.
  Retry 4 passed the owning-package case (1 passed, 93 deselected) at
  `/nix/store/hs6b8p1fzvl2cm9hm758f16qrbc7pygk-sqlite-verifier-test-surface-1`.
  It covers an aliased dependency without its own manifest, a nested unrelated
  lakefile/manifest, Lake's actual setup from another compiler working directory,
  and a relocated copy. Logs are `build/agent-logs/s7-files-nix-surface-{1,2,3,4}.log`.
  The two required local development builds passed; they are diagnostics, not
  acceptance evidence. Full/verdict and task-end gates have not run.
- 2026-10-24: a local source probe found an ownership ambiguity that current
  metadata cannot resolve: two consistent nested Lake packages with the same
  original name can compile the same Lean source. The nested build passes;
  the outer consumer's actual build then finds two roots. The Lake-generated
  manifest and both command results are retained in
  `build/agent-logs/package-root-probe/same-name-ambiguity.log` as diagnostic
  evidence. The owner is deciding the proposed source-relative root option and
  explicit-root reader. No option or restriction has been added. First-unit
  source commit/review remains pending this decision and the already-reported
  reviewer OAuth login failure; no review retry has been started.
