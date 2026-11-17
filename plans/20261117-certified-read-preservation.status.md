# Status of certified read preservation

Created 2026-11-17. Open. [Task](20261117-certified-read-preservation.task.md).

The task records the checker inputs, law and README acceptance cases.
The table frame of #412 is a prerequisite. KeptReadCheck.lean applies the read certificate using the table frame and the resolved schema.
The README sessions proof directly applies the law. Its proof directory now contains 693 lines,
down from 847 in #412. tests/surface_rebuild_test.py checks the two public claims and
the negative cases in KeptReadChecks.lean. The Nix checks are pending.

The proof module identifies the README claim that it certifies.
