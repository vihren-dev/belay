# Shop equivalence status

See [acceptance criteria](20261127-shop-last-output.task.md) and #359. The compiler lives in Programs/Claims and the end-to-end fixture is DeleteLastOutput. Scope includes porting the DELETE scan certificate onto the reviewed SELECT normalizer and replacing the earlier shop proofs.

The compiler now certifies plain DELETE counts and the surviving inputs of subsequent scans. Statement-local bindings are attached after normalization. CompiledDeleteCases and CompiledSelectCases cover the compiler boundary and plan comparison. The row-filter module is listed as core and imports the prelude.
