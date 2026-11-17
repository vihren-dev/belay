# Status of schema-only success

Created 2026-11-17. Open. [Task](20261117-schema-only-success.task.md).

The schema-only check and its mixed-script law now certify seven of the eight
rebuild statements. The copy at position three uses the row invariant. The
README example proof files went from 693 lines to 470. The regression in
`tests/surface_rebuild_test.py` builds the README claims and checks the
schema-only transaction and PRAGMA examples. The Nix checks are pending.

The task distinguishes the catalog-order restriction and the COMMIT check from the underlying execution laws.
