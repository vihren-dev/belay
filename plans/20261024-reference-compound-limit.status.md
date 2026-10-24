# Status: API reference compound SELECT limit

Created 2026-10-24. Status: DONE on 2026-10-24.
Task: [task file](20261024-reference-compound-limit.task.md).
Spec: ADR 0009 and the owner's PR #242 CI failure report.

## Current state

The owner reported that PR #241 passes and #242 fails the Linux API reference
build at 532 selected public modules. The recorded exception is in doc-gen4's
`read:transitive_imports`; its VALUES seed participates in a recursive UNION.
The patch preserves the root set and closure at the query boundary. The
compiled-reader regression, full 532-module reference, and 538-module descendant
stack reference pass. Post-review full/verdict, Nix integration and scheduled
checks pass. The coordinator handles publication of the accepted descendants.

## Progress

- Created isolated workspace `reference-compound-limit` on published #242
  head `975f31eb`. Compared `.envrc`, `shell.nix`, `tools/check_resources.py`
  and `nix/dev-shell.nix` with approved S4 `c0097b21`: every `cmp` exited 0.
  Under the owner's standing authorization, `direnv allow` exited 0.
- Assigned to `s4_part1` after task review. Its S7 proof-cost prototype remains
  safely preserved in its own workspace, with no active process. The urgent
  reference fix has separate source ownership and will update the existing
  stack by descendant commits, preserving all active workspaces.

## Failure evidence and review

PR #242 Linux check: [run 40113812092, job 120930821938](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40113812092/job/120930821938).
At 2026-10-24 17:07:02 UTC, the log records:
`Exception in read:transitive_imports after 0ms: too many terms in compound SELECT (error code: 1)`.
The failed fromDb invocation has 532 public module roots. PR #243's Linux check
also failed at [run 40115952880](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40115952880).
Review `20261024T173525Z-e5ac4243` has no musts and two should findings. The
record now uses durable CI evidence and names the shell comparison/authorization
checks. Both findings are fixed; implementation scope is unchanged.

- Review `20261024T173642Z-9725e388` has no findings. The task is handed to
  `s4_part1` for the narrow dependency fix and compiled-reader regression.
  Root coordinates heavy reference builds and descendant stack integration.

## Implementation and validation

- The pinned reader now uses `SELECT column1 FROM (VALUES ...)` as its
  recursive-query seed. Bound parameters and the recursive UNION are unchanged.
  The dependency revisions, caller, selected roots and core cache split stay
  fixed. ADR 0009 and the reference guide describe the additional observed
  failure and the patch's removal condition.
- Nix `docGen4` passed at
  `/nix/store/x66x56cw6qxvd72k056gldkvy7r0qv9i-sqlite-verifier-doc-gen4-4.34.1`.
  Its temporary native fixture calls `ReadDB.getTransitiveImports` in the
  compiled dependency. All 12 exact-closure cases pass: empty and unrelated
  inputs; 499, 500, 501, 532 and 640 roots; and duplicate-root variants with
  shared imports and a cycle. Equal lengths and both membership directions
  exclude missing, extra and duplicate returned modules.
- The original pinned reader's greater-than-500 failure is recorded in the
  PR #242 and #243 CI runs above. The patch is restricted to that query seed.
  The regression for this fix is the native `doCheck` fixture in
  `build-support/doc-gen4.nix`. Existing `tests/test_api_reference.py` and
  `tests/test_docgen_dependencies.py` guard the unchanged caller and dependency
  configuration; they do not exercise the repaired reader query.
- The coordinator confirmed the reviewed task's observed-failure contract for
  this urgent CI repair. The regression names that failure; the workaround
  keeps its durable CI URL, pinned source and removal condition. An upstream
  report is prepared but unpublished. This is a narrow interpretation of the
  workaround-report guidance, not a claim that an upstream issue exists.

- Implementation `caf53b680617e97487fe28c415a8f8200c4e9eb2` passed review
  `20261024T175710Z-caf53b68` with no musts and two should findings. The upstream
  report request is rejected under the coordinator's explicit interpretation
  above. The status now distinguishes the native regression from the existing
  caller/configuration checks.
- The sandboxed Linux `apiReferenceBase` build passed at
  `/nix/store/sc78xqcdj6z7d0sqlman4rpgnhxznsy9-sqlite-verifier-api-reference-base-2`.
  Its report contains 532 public modules and 41 recursor-link corrections.
  Inspection of this immutable Nix output found all 532 selected HTML pages
  and their expected source URIs. The existing cached-core split is intact.
  At this boundary, exact-commit source linking, final cadence and descendant
  stack reference acceptance were still pending; the results follow below.

- The exact-commit `apiReference` passed at
  `/nix/store/jqn6h8cij0xva91lb5sl3aqidndbjc3z-sqlite-verifier-api-reference-caf53b680617`.
  The report records 4,967 source links to the reviewed implementation commit.
  All 532 selected module pages contain their exact-commit source URI.
- The first final full invocation found the new `tests/docgen/` fixture absent
  from the repository's Lean file inventory. Registered it as a direct fixture;
  `tests/test_lean_categories.py` is the focused check. The compiled-reader and
  reference derivation inputs are unchanged. Final cadence reran after
  the registration correction's independent review, as recorded below.

## Final acceptance

- Registration correction `58fc6ba8056ae3ad61f98be613b0d880c79a9ad4` passed
  independent review `20261024T175949Z-58fc6ba8` with no findings.
- Post-review `just test-full` passed 808 Nix tests, report
  `/nix/store/8sp4gpizg8a919y90kjd6d856zpkrblx-sqlite-verifier-test-reports`.
  `just verdict` passed at
  `/nix/store/srv5lc3gnn1s9wzfjy1ilrzsb2ws0881-sqlite-verifier-verdict`,
  preserving all claims: 4,838 AGREE and 2,534 MODEL_UNSUPPORTED.
- `just test-nix` passed 70 integration checks. `just test-scheduled-checks`
  passed all 47 writer checks at
  `/nix/store/y595z61g5jqwxx0339lzr1mhv3iv1wfs-sqlite-verifier-scheduled-check-reports`.
  These ran sequentially in completed session 17338; no mutant suite ran.
- The final reviewed source's `apiReference` passed at
  `/nix/store/y8x4i9kf1k8jjrww2kqy1spr0aykixmg-sqlite-verifier-api-reference-58fc6ba8056a`: 532
  public modules, 41 recursor-link corrections and 4,967 source links to
  `58fc6ba8056ae3ad61f98be613b0d880c79a9ad4`. Its base is the checked output above.
- The coordinator merged the fix into the PR #243 descendant without rewriting
  shared ancestors. Its real sandboxed reference also passed at
  `/nix/store/iz8kjnq67dn05smyh3liv85rf2wwdzn5-sqlite-verifier-api-reference-d2ffeadbd472`: 538
  public modules, 41 corrections and 5,013 source links to
  `d2ffeadbd4720527e12c1e3615bed559e32f7fb0`. The coordinator checked every selected
  module's page and exact source URI. The report was also inspected here.
- The source patch, native regression, inventory and documentation are complete.
  Dependency pins, model semantics, corpora, claims and judge lock are unchanged.
  The task and status are marked DONE together. Stack publication and the
  larger ADR 0017 acceptance remain with the coordinator.
