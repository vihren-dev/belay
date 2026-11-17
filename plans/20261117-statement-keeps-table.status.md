# Status of table preservation

Created 2026-11-17. Open. [Task](20261117-statement-keeps-table.task.md).

The task records the accepted statement forms, the named rebuild checks
and the source laws. The local implementation is in place.

Issue #411 is the prerequisite for applying the check to the rebuild.

TableKeeps.lean checks resolved statements against the previous catalog.
TablePath.lean composes the single-step law, and SendSchemaPath.lean
exposes the final branch law. The README tracks customers and sessions
by computed positions. Its proof files total 847 lines, down from 1,001
in #411. RebuildTableFrames.lean and tests/surface_rebuild_test.py check
the surviving sessions and the rejected frames. Every resolved statement kind is listed explicitly, so a new kind requires a frame decision.
The Nix checks are pending.

The frame regression describes the expected position or refusal for each of its four scripts.

The model Lake library lists both frame modules. The package-boundary test in
tests/test_model_package.py checks that its manifest covers the import closure.
