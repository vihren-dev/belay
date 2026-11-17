# Status of multi-row UPDATE and transient unique keys

Created 2026-11-17. DONE. [Task](20261117-update-transient-keys.task.md).

The UPDATE branch in Schema/Dispatch/StatementStep.lean checks the final
table. Schema/Writes/RowUpdate.lean computes the updated rows in their
original positions. Schema/Rows/LiteralData.lean defines keyEqual.
Schema/Writes/DerivedColumnUpdateRun.lean proves the backfill is ready.
The existing diagnostic regression is in tests/surface_guide_test.py.

The plain UPDATE ready check compares the old and new keys of distinct rows.
The backfill proof uses the fact that its keys read only the original cells.
The test in tests/surface_update_transient_keys_test.py uses SQLite as the
oracle for the two conflicts and a successful write. The companion check in
tests/surface_guide_test.py covers final-table constraint diagnostics.
The task and implementation reviews are recorded under reviews/. The proof
sketch now describes the mixed-key check, and the module documentation names
the affected keys.

The locked Nix verdict produced the same report as main (88523528478c)
for all 7,868 cases. The subject result is
/nix/store/5dnimds0s7s0hxqfv7gkim7kncgj13j6-belay-verdict and the main
result is /nix/store/xky9nn88jn0hsm7zs0jg82m9sv18jmlm-belay-verdict.
The Linux full suite passed on the PR head 63cfaf8d79fd. It produced
/nix/store/p5bc27i20hdzf2h6bqmmjcq1bl1avmyg-belay-test-reports.
The Nix infrastructure suite passed all 98 tests. The scheduled checks passed
with /nix/store/l31i20shaxs0sa21vr303dq02dl4jfay-belay-scheduled-check-reports.
The full suite included both the pinned SQLite regression and the existing
final-table constraint diagnostics. The frozen verdict did not change.

[Linux full-suite log](https://github.com/vihren-dev/belay/actions/runs/44194328756/job/134431617789).
