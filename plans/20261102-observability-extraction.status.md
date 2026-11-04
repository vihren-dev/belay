# Observability extraction experiment status

Status: DONE, 2026-11-02. Created 2026-11-02. Audience: the team.

Task: [observability extraction](20261102-observability-extraction.task.md).
Workspace: `/home/codex/work/sqlite-verifier-observability` (`observability-experiments`).
Base: `187ea5104e7a1ae64477fc46b8e0e4743da27ae4` (`main` at creation).

## Progress

- Created the dedicated workspace. The owner approved `direnv allow` on 2026-11-02.
- Inspected the current collection points named in the task. The base contains
  the theorem-dependency exporter; reuse it rather than creating another exporter.
- Defined bounded experiments and the owner's supported-interface constraint.
- Specification review `20261102T080918Z-438f3719` had one should finding, rejected:
  R18 explicitly permits the owner's request as present-problem evidence.
- Sandboxed Python/review probes passed at
  `/nix/store/2r9z63n4m0v6pywnxz0ypjlg3k3qwy82-belay-observability-probes`.
  Public pytest hooks retain starts and completed phase events across abrupt exit;
  JUnit does not survive that exit. Review JSONL round-trip preserves statistics.
- The default Python 3.14 coverage core warns that it does not support dynamic
  contexts and misattributes a fixture line. The documented `core = ctrace`
  setting gives correct parent-process contexts. Child execution is collected
  but has no parent test context. Keep that limit explicit.
- Python/review implementation review `20261102T081521Z-3d7ee1f0`: no findings.
- Expanded sandboxed probes passed at
  `/nix/store/k4c23pmf0mmyrm3lv1kp8qps5137zhng-belay-observability-probes`.
  They cover Lean diagnostics, imports, native profiles, Lake invalidation,
  existing declaration exports and opt-in proof costs, CI envelope fixtures and
  semantic metadata. Ten existing review/report tests pass with the event plugin;
  their completion events agree with JUnit.
- The report and captured summaries are in `experiments/observability/README.md`
  and `results.json`. Host-daemon observations are labelled separately there.
  The report distinguishes measured mechanisms from production integration work.
- Implementation review `20261102T083255Z-b5d4340f` found no must findings and
  one should finding about inconsistent completion labels. The task, status and
  report now agree that the experiments are complete.
- All required extraction questions have measured results or explicit limits in
  the report. Production collection and deployment remain outside this task.
- Completion-record review `20261102T083353Z-77163b2d`: no findings.
  The temporary notes workspace was removed after its report joined the main line.
- Owner follow-up on 2026-11-02: publish the experiments and an observability ADR
  in the same PR. [ADR 0028](../docs/adr-0028-development-observability.md) is
  PROPOSED. It uses the captured results to specify continuous collection,
  ClickHouse delivery, history migration, retention and explicit limits.
  This adds a design proposal; production implementation has not started.
- ADR review `20261102T234641Z-8d3d10c8`: no findings.
- Owner revision on 2026-11-03: ADR 0028 now proposes an MVP for review history
  and local/CI test events. Invocation metadata is optional JSON, including `{}`;
  dedicated metadata columns and source-snapshot/dirty fields are withdrawn.
  Coverage, dependency/proof/mutation data, fixed retention and automatic reports
  are deferred. Detailed tables remain open for the owner's continued review.
  This documentation-only revision uses link and diff checks; the existing Nix
  evidence below is unchanged.
- Review attempt `20261103T104419Z-7ecac007` stopped at the reviewer's rate limit
  without a completed review. The owner instructed us on 2026-11-03 to skip the
  automated reviewer for this revision and will review it personally.
- Owner revision on 2026-11-04: replace ADR 0028 with a pytest-only proposal:
  a devops-managed ClickHouse instance and concrete two-table schema, reportlog
  enabled through shared pytest setup, and automatic local/CI upload and retry.
  Added [instructions for the devops maintainer](../docs/observability-devops-handoff.md).
  Review-history migration and coverage are outside this reduced scope. The
  proposal covers direct local pytest, shared Nix suites, scheduled/mutant jobs,
  failed-build artifacts and future tests inheriting the shared setup.
  This is a documentation change; production implementation and deployment have
  not started. The owner remains the reviewer for this ADR discussion.
  Local links, section anchors and whitespace checks passed. Cross-checked the
  design against shared pytest configuration, Nix suite construction, current CI
  entry points and upstream reportlog/ClickHouse documentation. Schema execution
  and uploader integration checks remain implementation acceptance work.
- Owner follow-up on 2026-11-04: distinguish permanent tests of our shared setup,
  uploader and schema from one-time commissioning demonstrations in ADR 0028.
  Apply R11/R15/R18 to this supporting code. Remove temporary demonstration suites
  and deployment probes after recording acceptance evidence; retain focused
  regression tests. Retiring research runners must preserve historical evidence
  and replay material. Existing JUnit summaries and review tooling remain in use.
  Updated the devops handoff to match. Documentation links, anchors and whitespace
  were checked; no production code or test behavior changed. Owner review applies.
- Owner clarification on 2026-11-04: the focused ClickHouse integration check uses
  the existing Nix suite machinery and dependency-based result reuse, not a new
  changed-path selector. ADR 0028 now specifies narrow inputs, a disposable server,
  an explicit devops schema/version pin, exclusion from duplicate host execution,
  and identity checks that do not run the database. Cache misses can still execute
  unchanged tests. Link, anchor and whitespace checks passed; this remains a
  documentation-only proposal reviewed by the owner.
- Owner instruction on 2026-11-04: add review rule R20 requiring expensive tests
  to evaluate and use the existing Nix result cache where appropriate. If it
  cannot fit, an explicit recorded owner decision must set the execution policy.
  Added the matching testing instruction to AGENTS.md and linked it from ADR 0028.
  Documentation and checklist-parser checks passed; no test implementation changed.

## References

- `experiments/observability/` will contain the explicit probes and report.
- `build-support/theorem-dependencies.nix` and `tools/theorem_dependencies.py`:
  existing declaration export.
- `tools/review_records.py`, `tools/review_stats.py`: review export and statistics.
- `build-support/tests.nix`, `tools/test_reports.py`: test results and reuse.
- ADR 0011 and ADR 0020: distinguish local observations from Nix evidence.

## Checks

`nix-build experiments/observability/default.nix -A probes` passed (sandbox enabled,
sandbox fallback disabled). This checks controlled pytest outcomes, selection,
abrupt exit, both coverage cores, subprocess coverage and real review round-trip.
The expanded target also checks Lean/Lake extraction, existing proof-cost and
dependency readers, metadata extraction and the plugin with repository tests.
The experiment does not add a collector to production tests or CI.

Before the PR, `just test-scheduled-checks` passed all 50 writer checks at
`/nix/store/b1970pfwpg9ks801732i7x6wrbixxjb4-sqlite-verifier-scheduled-check-reports`.
The suite report is
`/nix/store/r444x3c1521gin6g1bqmrx2if8rlfnwy-sqlite-verifier-test-writers-1/junit.xml`.
The required host Nix integration check `just test-nix` also completed: 71 passed.
Its cold run first needed the conformance runtime, then exceeded the recipe's
600-second limit after the local build-loop test passed. The warm rerun passed
in 204 seconds. These host checks are not conformance verdict evidence.
