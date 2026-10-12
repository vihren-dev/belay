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
- 2026-10-12: step 1. `.github/CODEOWNERS` has the two sections of ADR 0011;
  the review checklist has R16 (anchored integrity checks); ADR 0011 is
  ACCEPTED. R8 stays until the new `CODEOWNERS` is on `main` with enforcement.
- 2026-10-12: owner chose comparison in SQLite's catalog terms (option 1),
  after the finding that `native_replay.model_case` builds the reference
  tables with the frontend's translation of recorded schema SQL. The task file
  now names the renderer from model tables to PRAGMA rows (outcome 4).
- 2026-10-12: `judge/` (records, catalog form, comparison, outputs, claims,
  `python -m judge`), standard library only. It decodes every step of corpora
  v1 to v3 (177, 183 and 370 records). `tests/test_judge.py` checks an honest,
  a wrong, an evasive (all unsupported) and a broken stand-in subject. The
  subject writes predictions in the raw recorded form; the judge reduces both
  sides. Statement alignment uses SQLite's consumed byte ranges, as before.
  The live model cases stay outside the judge (task file updated).
- 2026-10-12: review fixes: empty tie groups agree when both results are empty (as in `Outputs.lean`), `tests/test_judge_outputs.py`; one constant for versions with outputs.
- 2026-10-12: subject predict command: `VerifierConformance/Predict.lean`
  (`conformance-runner --predict`), `conformance/predict.py`,
  `conformance/predict_render.py`. The renderer's catalog equals native SQLite
  for every admitted table shape (`tests/conformance_predict_test.py`).
- 2026-10-12: parity on corpora v1 to v3: the judge with the real subject and
  the current `classifyCase` path give the same verdict on all 730 cases; no
  catalog difference. `judge/claims.json`: AGREE floors v1 2, v2 8 (contains
  the 8 of `reports/20260929-adr4-corpus-v2-progress.json`), v3 11; no
  DISAGREE or HARNESS_ERROR on v1 to v5 and the synthetic workload. Full run on
  all six corpora: claims hold, 18 s on Linux. v4: 1264 and v5: 4376
  MODEL_UNSUPPORTED, as before.
- 2026-10-12: `nix/judge.nix` and `nix/judge.lock.json`. Refinement of
  outcome 6: the lock holds one content-derived store path per part (judge
  code with claims, each claimed corpus, the oracle `nix/sqlite.nix` with
  `nix/flake.lock`), not one derivation path per system: source paths do not
  depend on the system, and a mismatch names the part. The verdict
  (`nix-build nix/judge.nix -A verdict`, `just verdict`) runs the judge on the
  subject in the Nix sandbox; all claims hold. `tests/test_judge_lock.py`
  changes one byte of each part in a copy. Review finding
  20261012T090907Z-7c09b6c6#1 was only partly fixed: the runner-failure
  message has no test (it needs a broken runtime).
- 2026-10-12: owner chose: document memorized answers as a known limit in ADR 0011, add review condition R17 (advisory), and consider a hidden holdout corpus later.
