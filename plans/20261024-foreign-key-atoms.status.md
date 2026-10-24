# Status: foreign-key facts and preservation

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-foreign-key-atoms.task.md).
Specs: ADR 0022 slice 5; ADR 0017 S6; ADR 0018 foreign-key execution rules.
Inspected base: PR #239, `98a07bfe`, in `vihren-dev/sqlite-verifier`.

## Owner decision and evidence

On 2026-10-24 the owner chose: "Split parent-schema compatibility and
row-reference validity into separate atoms, then revise the foreign-key API
and proofs." This replaces ADR 0022 D3's unconditional foreign-key preservation
claim. The accepted amendment and required outcomes are in the task and ADR.

The prerequisite audit used the pinned SQLite 3.51.0 executable from Nix.
DROP INDEX succeeds with enforcement on for a referenced parent's unique index;
the following `foreign_key_check` fails at prepare with a mismatch. The audit
also observed the repeated-primary-key example in the task: child `(1,99)` is
accepted against parent `(1,2)` because the selected `(a,a)` key uses child `x`
twice. These observations informed the specification; no task acceptance check
has run and no model implementation has changed.

The task therefore supplies an explicit comparison mapping for row truth and
a separate catalog compatibility fact. The convenience path keeps current
engine selection. Supporting-index removal can preserve the first fact under
mapping transport while breaking the second. The representation is left to the
implementer, with these observable requirements fixed.

## Progress and relevant files

- 2026-10-24: inspected the existing FK atoms/checks and `Resolution/ParentKeys`;
  recorded accepted semantics, two acceptance parts and Nix coverage requirements.
  The task lists the implementation files.
- 2026-10-24: review `20261024T122036Z-c64a44ba` found no musts and one should:
  the historical owner-decision list still named one atom. That entry now names
  the two atoms and the amendment date. Implementation remains pending.
- Implementation must be assigned to a separate jj workspace after task review.
  Coordinate model barrels, statement laws and the surface database export with
  S4 and the query-source task. No concurrent edits to those surfaces are allowed.
  Later ALTER and view statements extend the preservation matrix; their absence
  from the current language does not satisfy those future obligations.
- 2026-10-24: follow-up review `20261024T122324Z-cf7aa9a6` had no findings.
  Assigned part 1 to agent `foreign_key_atoms` in workspace `fk-atoms`, based on
  `cf7aa9a6`. S4 confirmed the FK files and surface database export are disjoint
  from its remaining part 1. Model barrels remain reserved to S4 until a clean
  boundary. Heavy builds are coordinated with S4 and the build-boundary task.
