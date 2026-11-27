# Shop last-output equivalence (#359)

Status: DONE, 2026-11-27.

The shop regression states that deleting orders without customers and reading big orders has the same last output as the reference SELECT. Its proof is a single `sql_run`. The previous write/read postcondition and its shop-specific proof infrastructure are retired. The standalone abstract-database write regression remains.

The surface suite must compare the two compiled plans, check statement-local bindings, NULL survival, duplicates and independent tables, and decline unsupported write effects. The compiler certificate must account for each execution branch from a database with the catalog. SQL NOT and the Boolean complement of WHERE differ on NULL.
