# Status: S6 foundations prototype

Created 2026-10-24. Status: OPEN. The checked prototype is implemented; independent review and
task-end acceptance remain.
Task: [task file](20261024-surface-s6-foundations.task.md).
Specs: ADR 0017 S6; product guide questions 2/4/11/12/13, with source revision
and required behavior recorded in the task.

## Current evidence

The coordinator inspected the pinned Lean 4.34.1 `Std.Do` sources:
`WP` interprets programs as predicate transformers; `WPMonad` requires a lawful
monad and preservation of pure/bind. Those class declarations do not establish
that an instance agrees with SQLite execution. `WPSound` supplies another
library-level soundness interface whose applicability must be checked.

Current `Sql.runFrom` carries a complete connection and a statement index.
The public run includes final pragma settings and an open-transaction snapshot;
the underlying connection also carries counters. This motivates the equivalence
audit; no congruence counterexample or prototype theorem has been checked yet.
The guide explicitly identifies hidden state, `before` without ATTACH and
experimental `mvcgen` as open questions. This task preserves them as decisions
until the prototype has evidence.

## Progress

- 2026-10-24: specified a bounded experiment to inform S6. It will use
  S4's final monad and universal execution interfaces, so implementation waits
  for those interfaces. The full S6 task is still to be specified afterward.
  No Nix acceptance result is claimed.
- 2026-10-24: review `20261024T123255Z-22140c04` found no musts and one should:
  the ADR identifies questions needing a prototype, rather than specifying its
  exact scheduling. Corrected that attribution; this task's prerequisite on
  final S4 interfaces remains a planning choice.
- 2026-10-24: made the S4 dependency explicit for both actual raw `oneOf`
  continuations and every concrete `rows` continuation, following the reviewed
  S4 task clarification `9f6cba9b`. The prototype still waits for reviewed code.
- 2026-10-24: isolated workspace based on reviewed S4 success commit
  `00c8707f5a4023fb97e5e8259f5560296efe12f3`. Its review had no findings.
  Available inputs include `Env.Complete`, `Sql.SucceedsFrom`, `Succeeds`,
  its allOk/script/send laws, `LawfulMonad Sql` and `Sql.runFrom_bind`.
  S4 retains ownership of these production files; this task consumes them.
  Prototype implementation remains pending this carried task's review.
- 2026-10-24: carry review `20261024T133240Z-516f71f6` had no musts and
  three shoulds. The task now names the S6 migration-postcondition and
  commutation-automation contracts blocked by guide questions 4 and 13.
  S4's clean review record `20261024T133008Z-00c8707f` is carried with the
  prototype task so its stated prerequisite can be checked in this workspace.
- 2026-10-24: follow-up review `20261024T133349Z-62320bf0` had no musts
  and two shoulds. Explicitly marked the audit scope as extending the question
  numbers named in ADR17's S6 row. Removed the future-S8 justification; the
  current S6 contracts remain the reasons for both audits.

- 2026-10-24: implemented five isolated fixtures, their one Nix surface-suite
  test, and `docs/s6-foundations-findings.md`. The transformer delegates all SQL
  steps to existing execution. Its bind law, S4 top-postcondition equivalence,
  complete-environment quantification and actual-run soundness are proved.
  The same SQL-write triple uses mvcgen and explicit pure/bind lemmas. Fixtures
  cover all required contexts, both kinds of oneOf continuation, error policies,
  hidden-state counterexamples, both bind-congruence directions, and footprint
  counterexamples. AUTOINCREMENT and the before qualifier remain checked
  frontend rejections. No production package, semantics or judge claim changed.
- 2026-10-24: the first Nix surface attempt found the inherited S4 helper-input
  omission. Carried only the one-line source registration from reviewed
  `b90086830a4eeb23b69ef943728f5c8f2648029a`, plus its clean review record,
  without rebasing or copying S4's later work. The corrected Nix surface suite
  passed all 56 tests in 106.10 seconds, including the prototype's 28 axiom
  reports (only propext, Classical.choice and Quot.sound permitted).
  Command: `direnv exec . timeout 1500 nix-build build-support/default.nix -A
  tests.surface --out-link build/s6-surface-tests --option sandbox true --option
  sandbox-fallback false --extra-experimental-features 'nix-command flakes'`.
  Output: `/nix/store/2dlm2j0i3wxs2cccdipzr2qidqiyig1n-sqlite-verifier-test-surface-1`.
  Log: `build/agent-logs/s6-surface-tests-2.log`. No package file changed, so
  the per-package dev-build gate does not apply. Local probes were diagnostic
  only; this Nix-selected fixture is the acceptance evidence.

- 2026-10-24: review `20261024T140808Z-e9a0354d` found no musts and two
  shoulds: enumerate Output constructors in the transformer and raw-wrapper
  fixture. Both are fixed. Self-review also named the axiom allowlist and added
  module descriptions. The same Nix surface command passed all 56 tests again
  at `/nix/store/1rzb9hwr5s7yccpwjx2xiwbzja3bcd99-sqlite-verifier-test-surface-1`;
  log `build/agent-logs/s6-surface-tests-3.log`. Nix's computed judge identity
  still matches all 55 locked components. The proof and program observations
  are unchanged. Independent review of this refactor follows.
- 2026-10-24: refactor review `20261024T141327Z-6c26ac21` found no musts
  or shoulds. Tightened the design record after coordinator review: the only
  demonstrated semantic owner judgment concerns visible equivalence versus
  composition. The proposed production relation retains actual runs and all
  branch outcomes, including failed and unmodeled alternative traces. The
  before context is required model work; whole-trace fresh-run ifOk and direct
  frame lemmas are routine implementation choices. No prototype source changed;
  the latest Nix surface acceptance still applies. Task-boundary gates remain
  queued behind the other agents' builds.
- 2026-10-24: design review `20261024T141906Z-21b80e17` found no musts
  and one should: state which guide meanings the before/ifOk recommendations
  retain. The record now identifies the fixed-start read-only lookup and
  whole-program failure disjunction explicitly, and reserves changed meanings
  for owner judgment. This is documentation only; Nix fixture inputs are unchanged.
- 2026-10-24: wording review `20261024T142000Z-a49073a6` found no musts
  and one should: qualify the ifOk disjunction with modeled execution. The design
  record now repeats the task's all-branch modeled-execution premise and states
  that an unmodeled outcome never discharges ifOk.
- 2026-10-24: follow-up review `20261024T142127Z-a3cffcb5` found no musts
  or shoulds. The owner accepted the recommended production meaning: `≈` uses
  full context and all branch outcomes, including failed/unmodeled alternative
  traces, with separately named weaker visible observations. The design record
  marks this decision accepted; the prototype implementation is unchanged.
  Separately, the coordinator's native audit of INSERT and purge guide examples
  found trigger counterexamples. The owner accepted explicit schema and trigger/FK
  effect premises for those universal claims; that guide correction is outside
  this bounded prototype. The full task gate is running, with later verdict,
  Nix identity and scheduled checks queued. No task completion is claimed yet.
