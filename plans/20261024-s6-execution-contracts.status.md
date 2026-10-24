# Status: S6 execution and proof contracts

Created 2026-10-24. Status: OPEN. First production unit is checked and reviewed; later contracts remain open.
Task: [task file](20261024-s6-execution-contracts.task.md).
Specs: ADR17's S6 row, the owner decision of 2026-10-24 recorded below,
and the checked S6 foundations.

## Prerequisites and scope

The owner accepted full actual and branch-outcome equivalence on 2026-10-24.
The prototype proves the relevant generic transformer laws, but its original
instance rejects SQL errors and its equivalence omits failed alternative traces.
Production must support conditional triples and retain those traces explicitly.

Final S4 interfaces and the prototype are published. The task is refreshed
for assignment to `text_build_boundaries` in a separate workspace on PR #248.
Its modules remain separate from FK and query-context implementation work.
The accepted quiet observation view affects later migration patterns,
not these complete-execution semantics. No production or acceptance result
is claimed by this task file.

## Progress

- 2026-10-24: specified exact execution branches, operationally sound Std.Do
  primitives, conditional/total success bridges and compositional equivalence.
  Two acceptance parts retain the ordinary model interpreter and S4 contracts.
  The public assertion/pattern/automation task remains to be specified.
- 2026-10-24: review `20261024T144607Z-9eeac73e` found no musts and two
  shoulds about unavailable inputs in the planning tree. The task now names
  the unmerged S4 and prototype workspaces and exact reviewed commits. Also
  replaced a reference to transaction helpers with the existing explicit
  BEGIN/COMMIT/ROLLBACK programs; ADR17 still defers withTransaction.
- 2026-10-24: follow-up review `20261024T144839Z-5684010b` has no findings.
  Implementation remains unassigned and waits for final S4 interfaces.

- 2026-10-24: refreshed the handoff to published #248 `e3d6aa38`, which contains
  completed S4 #244 and S6 prototype #246. Removed stale workspace and pending
  validity-check references. Made the accepted fresh-run helper/ordinary-triple
  equivalence explicit. The owner accepted that contract earlier; this refresh
  adds no scope decision. The FK owner confirmed that generic branch/WP/equality
  work can proceed independently while remaining FK checks run. Assignment
  follows review of this refresh; heavy checks require the coordinator's slot.
- Handoff refresh `7e855ae9` passed independent review
  `20261024T204324Z-7e855ae9` with no findings. Root verified the named completed
  sources in published #248; the planning tree itself retains older model code.
  Assigned to `text_build_boundaries` in `sqlite-verifier-s6-execution` on
  `e3d6aa38`, alongside its independent FK acceptance work. Implementation owns
  new surface execution-context/branch/WP/equivalence modules and their fixtures.
  Shared barrel and suite-registration additions must stay narrow; S5 owns its
  counterexample/search modules. No production implementation is claimed yet.

- Isolated implementation workspace `s6-execution` starts at published PR #248
  `e3d6aa388eeb070b94cdcf34a474f79f692d3c12`. The task, status and clean
  review `20261024T204324Z-7e855ae9` were copied from planning commit
  `881c975f`; no other planning ancestors were carried. The approved `.envrc`
  and `shell.nix` match the existing development workspace byte for byte.

- Carry review `20261024T204857Z-ac33b102` had no musts and two shoulds.
  The task now cites this dated owner-decision record instead of implying that
  ADR17 already contains the later S6 clarification. The header now distinguishes
  the completed handoff from production implementation. Both findings are fixed.

- The first production unit adds an exact relation over existing `SqlRun` results,
  retaining stopped outcomes and every actual/concrete continuation. Its pure,
  step, bind, actual-membership and validity laws use `runScriptStep`. The
  transformer quantifies over those branches; its standard `WPMonad` instance
  has separate actual and all-branch soundness theorems. Local Lean probes compile
  these contracts. The installed Nix acceptance below checks this unit. Conditional/total policies,
  S4 bridges, fresh triples and strong equivalence remain open.
- Review `20261024T205000Z-d265f0c7` had no musts and one should: the status's
  specification line still implied ADR17 contained the later owner decision.
  Corrected that citation and recorded the finding as fixed. This unit selectively
  carries the accepted complete-outcome and fresh-entry paragraphs from planning
  `297c125c` into ADR17, preserving the published S4 validity-removal wording and
  omitting links to future task files absent from this branch.

## Exact branches and modeled-execution transformer

The first coherent source unit contains ExecutionContext, ExecutionBranches,
ExecutionBranchLaws, ExecutionBind, ExecutionWP, ExecutionStep and ExecutionWPLaws.
Each module is below 100 lines. The branch relation reuses complete `SqlRun`
results and `runScriptStep`. Its actual-run membership prevents an empty branch
set from proving a transformer vacuously. The finite check instance is derived
from the exact relation; it does not execute a second model interpreter.

Nix acceptance: `direnv exec . bash build/agent-logs/s6-first-unit-gates.sh`
ran `timeout 1500 just dev-build`, then sandboxed `nix-build` of
`project.tests.surface.overrideAttrs` with `PYTEST_ADDOPTS` selecting
`execution_branches_and_wp or s6_transformer_agrees_with_execution` and a finite
1800-second command timeout. Command-local Nix settings retain the configured
values and set max-jobs=1 and cores=2. The development build passed as a diagnostic.
The Nix result is:
`/nix/store/9mh19n9lvn425dfn9s9hdbbjcwcdf732-sqlite-verifier-test-surface-1`.
Both tests passed, 79 were deselected, in 12.58 seconds. The two new installed
fixtures audit 32 declarations; the retained prototype audits 28. Every report
uses only propext, Classical.choice and Quot.sound. Logs are
`build/agent-logs/s6-first-unit-{dev-build,nix-surface}-1.log`.

The new fixtures cover both proof routes for a real write, raw and concrete LIMIT
choices, repeated and empty choices, stopped bind, errors followed by a write or
an unmodeled stop, and clock/counter/snapshot retention. Duplicate alternatives
add no concrete rows choices; their actual raw wrapper remains observable.
This is a coherent-unit gate, not either acceptance part's full/verdict gate.
Conditional/total policies, exact S4 bridges, fresh helpers, strong equivalence
and the remaining compositional fixtures remain OPEN.

Independent review `20261024T210916Z-e5d737bd` of source
`e5d737bd4a9e50b8d58582bd3b1b2c016d99527b` found zero musts and zero shoulds.
This coherent branch/WP unit is at rest. The task and both broader acceptance
parts remain open until their remaining contracts and final gates are complete.

## Success policies and explicit fresh entry

The second coherent unit adds ExecutionSuccess and ExecutionFresh. `andOk`
requires an error-free whole trace and the final property; `ifOk` requires the
property only when that trace is error-free. Both retain modeled execution of
every branch. An existing error or unmodeled output in the prefix removes the
conditional property's obligation but cannot excuse a new unmodeled step.
At an empty prefix, total success with a true postcondition is exactly
`Sql.SucceedsFrom` at the same clock, index and full connection.

`FreshTriple` quantifies valid bundled databases satisfying its predicate and
complete environments, then fixes the empty trace, index zero and new connection.
Its postcondition can retain the initial database and environment. It is exactly
a family of ordinary `Std.Do` triples with those explicit entry assumptions;
ordinary triples still quantify arbitrary contexts. Separate actual and branch
soundness laws and an exact universal S4 `Succeeds` bridge are checked.
No default-environment observation is substituted for that quantifier.

Nix acceptance: `direnv exec . bash build/agent-logs/s6-success-unit-gates.sh`
ran the mandatory bounded development build, then the same sandboxed surface
selection as the first unit. Command-local settings preserve Nix configuration
and set max-jobs=1 and cores=2. The Nix result is
`/nix/store/gm2y6fiagq0jcngxjxq089kbfcfrvhi7-sqlite-verifier-test-surface-1`:
2 tests passed, 79 deselected, in 14.21 seconds. The three production fixtures
audit 54 declarations, and the five retained prototype fixtures audit 28;
all reports use only propext, Classical.choice and Quot.sound. The new fixture
covers conditional versus total errors, error then unmodeled, both non-OK prefix
kinds, raw/concrete branch obligations, nonzero-index bridging, fresh entry and
a refuted arbitrary-context freshness claim. Both production modules are under
100 lines. The development build passed as a diagnostic; it is not acceptance
evidence. Logs are `build/agent-logs/s6-success-unit-{dev-build,nix-surface}-1.log`.

This closes the source work for the first acceptance part's operational bridges.
Independent review and its full/verdict gate remain due. The equivalence and
compositional helper part, task-end gates and overall task remain OPEN.

Independent review `20261024T212855Z-1c09bf9f` of the success/fresh source
`1c09bf9f` found zero musts and zero shoulds. It covered all seven changed files.
The first acceptance part is ready for its required full/verdict gate; that gate
has not yet run. Strong equivalence and the rest of the task remain OPEN.
