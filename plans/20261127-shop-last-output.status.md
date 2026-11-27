# Shop equivalence status

Status: DONE, 2026-11-27.

See [acceptance criteria](20261127-shop-last-output.task.md) and #359. The compiler lives in Programs/Claims and the end-to-end fixture is DeleteLastOutput. Scope includes porting the DELETE scan certificate onto the reviewed SELECT normalizer and replacing the earlier shop proofs.

The compiler now certifies plain DELETE counts and the surviving inputs of subsequent scans. Statement-local bindings are attached after normalization. CompiledDeleteCases and CompiledSelectCases cover the compiler boundary and plan comparison. The row-filter module is listed as core and imports the prelude.

DeleteLastOutput now proves the shop claim with one sql_run and checks equality of the compiled plans by reflexivity. The old big_after_delete and its manual comparison fixture have been retired. SelectContextCases keeps the standalone write regression. RowFilterCases keeps the independent disjointness and NULL-survival laws.
