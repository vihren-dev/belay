# Status: foreign-key facts and preservation

Created 2026-10-24. Status: OPEN. The enforced-DROP proof unit is checked and
reviewed; remaining DDL/run work and complete acceptance are unfinished.
Task: [task file](20261024-foreign-key-atoms.task.md).
Specs: ADR 0022 slice 5; ADR 0017 S6; ADR 0018 foreign-key execution rules.
Inspected base: PR #239, `98a07bfe`, in `vihren-dev/sqlite-verifier`.

Latest scope decision, 2026-10-25: the owner accepted correcting ADD COLUMN
REFERENCES defaults, including empty/nonempty tables, enforcement on/off and
literal-NULL versus NULL-valued expression distinctions. ADR22 and the task are
amended together. Native evidence is retained in the FK workspace's
`build/agent-logs/add-reference-{native.json,model.log,default-spelling-native.json}`.
The enforced-DROP unit is already checked/reviewed at `ffe4d749`; this new
execution correction has no implementation or acceptance claim yet. The task
amendment review `20261025T015343Z-fc22761c` found no musts and one R19 should:
name the new correction in the acceptance-part list. The list now places it
with the remaining DDL/run part. The amended task awaits final review before
implementation resumes in an available slot.

Prior scope decision, 2026-10-24: the owner accepted selected action targets
for CASCADE/SET NULL/SET DEFAULT and their assigned/changed-column effects.
Native diagnostics show repeated-key actions leave an unused child column
unchanged and do not fire its UPDATE OF trigger. The earlier model wrote that
column too. The revised task requires regression evidence and ordinary-mapping
coverage. The focused native Nix gate now passes; full part acceptance remains.

Review `20261024T151438Z-4c59fcc3` found no musts and two wording shoulds:
name both execution corrections in the acceptance boundary and state explicitly
that the action-target correction had not started at that boundary. Both were corrected.

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
- Implementation was assigned to a separate jj workspace after task review.
  Coordinate model barrels, statement laws and the surface database export with
  S4 and the query-source task. No concurrent edits to those surfaces are allowed.
  Later ALTER and view statements extend the preservation matrix; their absence
  from the current language does not satisfy those future obligations.
- 2026-10-24: follow-up review `20261024T122324Z-cf7aa9a6` had no findings.
  Assigned part 1 to agent `foreign_key_atoms` in workspace `fk-atoms`, based on
  `cf7aa9a6`. S4 confirmed the FK files and surface database export are disjoint
  from its remaining part 1. Model barrels remain reserved to S4 until a clean
  boundary. Heavy builds are coordinated with S4 and the build-boundary task.
- 2026-10-24: the owner accepted the mapped-NULL engine correction after native
  evidence showed the old helper accepted `(99,NULL)` for the repeated `(a,a)`
  parent key and omitted its pragma violation. The revised task corrects the
  shared helper first, updates default mappings/proofs, and requires native
  regressions. Selected child columns determine NULL exemption; missing or
  mismatched targets retain the declaration-column fallback. The working API
  split is preserved in `sqlite-verifier-fk-atoms`. Agent `text_build_boundaries`
  has resumed it and adapted the helper, mapping proofs and native cases;
  model/Nix checks remain. Native-only replay is diagnostic, not acceptance.
- 2026-10-24: pinned native replay found an enforced parent replacement that
  leaves an orphan because child-scan and parent-lookup affinities differ.
  Added the necessity example and explicit comparison-consistency premise to
  the existing conditional preservation contract. This is within the accepted
  schema/mapping/effect conditions, not another engine change or an assumed
  final atom. The owner was informed; part 1 and independent work continue.
- The accepted action scope is carried at `1a10a3c8`, with clean follow-up
  review `20261024T152329Z-01a02bef`. Resolution and execution share the selected
  child projection. Trigger preparation reads assigned columns; generated
  dependencies feed FK constraint checks. The Nix native gate passed all 35
  differential/kernel cases at
  `/nix/store/mhvsqdz6wnx66s0rr80a12yp5xam6hif-sqlite-verifier-test-model-1`.
  Surface/mutant Nix gates and part-1 full/verdict remain open. Part 2's global
  counter invariant and statement/run preservation are still implementation work.
