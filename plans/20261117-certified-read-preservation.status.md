# Status of certified read preservation

Created 2026-11-17. DONE. [Task](20261117-certified-read-preservation.task.md).

The task records the checker inputs, law and README acceptance cases.
The table frame of #412 is a prerequisite. KeptReadCheck.lean applies the read certificate using the table frame and the resolved schema.
The README sessions proof directly applies the law. Its proof directory now contains 693 lines,
down from 847 in #412. tests/surface_rebuild_test.py checks the two public claims and
the negative cases in KeptReadChecks.lean.

The proof module identifies the README claim that it certifies.

The [hosted verdict](https://github.com/vihren-dev/belay/actions/runs/44212432475)
matches the baseline on all 7,868 frozen cases. At stack head
761208cf244b, all 1,483 tests in the 22 Nix reports passed, including
the README rebuild proofs. All 98 infrastructure tests and the scheduled
checks passed on that head.
