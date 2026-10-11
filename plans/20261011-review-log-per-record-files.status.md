# Review log per-record files status

Created 2026-10-11. Status: DONE (step 1; steps 2 and 3 are separate).
Task: [20261011-review-log-per-record-files.task.md](20261011-review-log-per-record-files.task.md).

## References

- Process: `AGENTS.md` (review section), `docs/ci.md` (review log check),
  `plans/20261006-review-process.task.md`.
- Sources: `tools/review_log.py`, `tools/review.py`, `tools/review_stats.py`,
  `tools/review_log_check.py`, `tests/ci_scope.py`, `.github/workflows/ci.yml`,
  `justfile`.
- Tests: `tests/test_review_log.py`, `tests/test_review_log_check.py`,
  `tests/test_review_stats.py`, `tests/test_review.py`, `tests/test_ci_scope.py`.

## Progress

- 2026-10-11: task and status files created.
- 2026-10-11: `tools/review_records.py` stores each review and resolution in
  its own file; `review`, `review-resolve`, `review-stats`, the CI check and CI
  scope use it. `AGENTS.md` and `docs/ci.md` updated. Review-tool tests pass
  (51). The source suite has 6 Lean compilation failures that also fail on
  unchanged `main` in this checkout.
- 2026-10-11: real `just review` of that commit wrote
  `reviews/20261011T105958Z-d6909b37/review.json` and left `log.jsonl`
  unchanged. Finding 1 (reject new frozen-log lines) rejected: the owner's
  step 2 needs them. Findings 2 and 3 (docstring purpose) fixed.
- 2026-10-11: `just review-log-frozen` (`tools/review_log_frozen.py`). First
  real run: 19 unmerged branches and workspaces, 9 with frozen-log lines that
  `main` lacks (they need step 2). Task outcome 6 refined: older logs on stale
  branches do not block step 3.
- 2026-10-11: review of the frozen report: two "should" findings (test
  docstrings name their subject; error actions match the failure) fixed.
- 2026-10-11: second review round of the error messages: two "should"
  findings fixed (a separate message for a jj timeout; tests for the missing-jj
  and outside-a-repository errors). Third round: a test for the timeout
  message, with `subprocess.run` patched in-process.
- 2026-10-11: last review clean. Step 1 DONE. Next: step 2 (merge to `main`,
  rebase open branches and workspaces), then step 3 when
  `just review-log-frozen` exits 0.
- 2026-10-11: step 2 done. #85 merged. Branches #81, #76, #80 and #74 were
  rebased onto `main` and their frozen-log lines moved to record files; #60
  (`t06-bundle-readiness`) got a merge of `main` with a port to the two
  trusted Lean roots. `just review-log-frozen` then exited 0. Step 3:
  `plans/20261011-review-log-conversion.task.md`.
