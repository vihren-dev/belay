# Development integrity status

Created 2026-10-12. Status: OPEN.
Task: [20261012-development-integrity.task.md](20261012-development-integrity.task.md).
Decision: [ADR 0011](../docs/adr-0011-product-trust-and-development-integrity.md).

## References

- Enforcement: ruleset 23934665 (owner changed it on 2026-10-12),
  `.github/CODEOWNERS`, `docs/review-checklist.md`.
- Current judge: `conformance/corpus.py`, `conformance/native_replay.py`,
  `conformance/model_check.py`, `conformance/replay_tiers.py`,
  `ConformanceRunner.lean`, `VerifierConformance/Case.lean`,
  `VerifierConformance/Outputs.lean`, `VerifierConformance/Json.lean`.
- Nix: `build-support/default.nix`, `build-support/tests.nix`,
  `build-support/sources.nix`, `nix/sqlite.nix`, `nix/flake.nix`.
- Current claims: `tests/conformance_upstream_test.py`,
  `tests/conformance_coverage_test.py`, `tests/conformance_progress_views_test.py`,
  `tests/conformance_sample_test.py`, `reports/20260929-adr4-corpus-v2-progress.json`.

## Plan (informal, may change)

1. `CODEOWNERS` sections and the anchoring condition (outcomes 1, 2 without
   the R8 removal); ADR status.
2. R8 removal, after enforcement is confirmed on the new `CODEOWNERS`.
3. Claims file.
4. Judge and parity with `classifyCase`.
5. Subject predict command.
6. Judge derivation, lock and enforcing Nix file.
7. Verdict job and required check.
8. Removal of checks without an anchor.

## Progress

- 2026-10-12: task and status files created. Ruleset 23934665 confirmed:
  `require_code_owner_review: true`, one required approval, stale approvals
  dismissed on push.
