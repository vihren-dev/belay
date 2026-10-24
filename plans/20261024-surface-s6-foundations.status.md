# Status: S6 foundations prototype

Created 2026-10-24. Status: OPEN. Implementation has not started.
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
