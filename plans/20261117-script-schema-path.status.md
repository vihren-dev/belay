# Status of the script schema path

Created 2026-11-17. Open. [Task](20261117-script-schema-path.task.md).

SchemaPathStep.lean proves resolution-state agreement for each successful
execution. SchemaPath.lean gives the resolved statement at every prefix.
SendSchemaPath.lean applies these laws to every successful branch. Both
README proofs use resolutionAt for intermediate states and retain the
same public claims. tests/surface_rebuild_test.py checks each proof.
The final stack runs of just test-full, just test-nix and just test-scheduled-checks are pending.

The ten Lean proof files in examples/table-rebuild/Proof contain 1,001
lines, down from 1,038 before the change.

The example describes resolution from the prefix certificate at the copy and the final read.

The core Lake library now lists SchemaPath and SchemaPathStep explicitly.
tests/test_model_package.py compares the Lake module inventory with the model
root's import closure. The locked Nix verdict matched main on all 7,868 cases.
