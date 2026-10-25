# Retain the first hosted mutation failure

Created 2026-10-25. Status: OPEN.
Audience: implementers and reviewers.
Progress: [status](20261025-mutant-failure-diagnostics.status.md).
Inspected base: published PR #251, `fe169099`.

## Present problem

The general-mutant jobs of PRs #249 and #250 report failed query, fromless and
JSON-function tests, then continue until the outer deadline. The interruption
prevents pytest's final failure details and JUnit report from being retained.
The exact query/JSON causes therefore remain unconfirmed despite successful
separate local reproductions. PR #251 fixes only the confirmed fromless fault.
The #250 log is retained in the workspace research notes as
`Lean model modularity investigation/ci249-mutants/ci250-mutants.log`;
the hosted run/job are `40146867734` / `121029975402`.

## Required outcomes

- When pytest has reported a failed test in one of the three mutant suites,
  that suite ends with its failure diagnostics and a failing exit status.
  Later test groups do not consume the remaining suite budget before pytest
  prints the already available failure information. This does not promise
  diagnostics from a test that has not returned or produced a failure report.
- A successful mutant suite executes the same complete selected inventory,
  with the same native baseline agreement, exact mutation anchors and kill
  assertions. No mutant, target or guard is removed or weakened. No timeout
  is increased. Independent CI matrix jobs retain their current policy.
- Ordinary non-mutant suites retain their current execution policy. Both
  local named selections and hosted mutation jobs use the same configured
  Nix suite boundary. Use existing pytest facilities; do not add a plugin,
  custom report format, logging framework or second runner.
- Production packages, native cases, corpora, judge claims, lock and oracle
  sources remain unchanged. This change exposes failures; it does not claim
  that the unconfirmed query/JSON failures or suite duration are repaired.

## Tests and acceptance

Inspect the evaluated Nix install commands for all three mutant suites and
representative ordinary suites. The former have the early-failure behavior;
the latter keep their existing commands. Compare their selected test inventories
and unchanged limit values. Run the existing suite-routing/ownership checks;
do not add a test of pytest's own implementation merely to check its documented
flag. Relevant named mutation checks may be reused only when their exact
derivation or complete tested input closure is unchanged. Never run the broad
mutation suite locally.

The single acceptance part requires independent review, post-review
`just test-full` and `just verdict`, then `just test-nix` and
`just test-scheduled-checks`. The owner's standing instruction excludes broad
local mutation runs, so this replaces `just test-scheduled` here. Compare
protected source trees and frozen predictions. Record only Nix results as
acceptance evidence. After publication, use the existing manual CI trigger to
run the hosted mutation suites: the ordinary pull-request change filter skips
them for this build-support change. Inspect actual test execution, not only job
status, and retain any newly exposed failure details. Repairs for those causes
are separate work.

## Relevant code and constraints

`build-support/tests.nix` constructs the shared suite command and the
`mutants`, `tableMutants` and `functionMutants` derivations. Their inventory is
in `tests/nix_suites.json` and `tests/nix_mutant_suites.json`. `justfile` and
`.github/workflows/ci.yml` supply the outer bounded invocation. Existing
suite ownership/routing tests protect those boundaries. Keep the change on
published #251 so it can be released without unfinished view or S5 work.

The separate view workspace remains frozen at its reviewed harness integration
while this task is active. Do not rewrite shared ancestors or change a running
acceptance source. All subprocess checks retain finite timeouts.
