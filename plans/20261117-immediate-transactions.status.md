# Status of immediate transactions

Created 2026-11-17. Open. [Task](20261117-immediate-transactions.task.md).

Grammar.Writes now sends all four parsed BEGIN modes through the same snapshot
operation. The profile gate admits recorded immediate mode. Translation, profile
admission and native replay are covered by syntax_mapping_test.py,
profile_scope_test.py and conformance_profile_test.py. The locked verdict and
full Nix gates are pending.

The task distinguishes the recorded modes from direct SQL, which also accepts EXCLUSIVE.

The profile-scope module documents all three settings that still receive a refusal.
