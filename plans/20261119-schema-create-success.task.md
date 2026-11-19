# Schema-only success for catalog creation

Created 2026-11-19. Open. [Belay issue 444](https://github.com/vihren-dev/belay/issues/444).

For any valid connection, resolution to CREATE TABLE, CREATE VIEW, CREATE
TRIGGER or non-unique CREATE INDEX guarantees that the script step continues
with one execution and a successful output. A caller can use one law for all
four forms. Keep the raw rules for a particular statement. The existing
schema-only success check must certify these steps. A UNIQUE index still
needs a proof about the rows. A prepare error gives no success certificate.

The DROP COLUMN guard in `Schema/Ddl/DatabaseDropColumn.lean` reads only the
catalog. Its successful resolver outcome gives both droppability and the
exact catalog after removal. Certify this resolved step from the schema as well. The existing data-dependent ADD COLUMN errors
must still be possible.

## Acceptance

Compile a public `Script.succeeds_of_schema` proof for a migration with a
view, a trigger, and a non-unique index. Exercise the UNIQUE case separately
so that accepting it for arbitrary rows fails a test. On the corrected
`SplitByAge` migration, check the entire resolved path and show that only
its two INSERT FROM SELECT statements need hand proofs. Verify that a
resolved DROP COLUMN on a table with a removable column is certified. Use the actual script
in the surface fixture. Run the repository acceptance checks.

This task depends on the catalog guards requested in #443. The step check
also sees transaction state. A true result must imply success for each
valid connection that has the input resolution state.
