# Status of immediate transactions

Created 2026-11-17. Open. [Task](20261117-immediate-transactions.task.md).

Grammar.Writes now sends all four parsed BEGIN modes through the same snapshot
operation. The profile gate admits recorded immediate mode. Translation, profile
admission and native replay are covered by syntax_mapping_test.py,
profile_scope_test.py and conformance_profile_test.py. The full Nix gates are pending.

The task distinguishes the recorded modes from direct SQL, which also accepts EXCLUSIVE.

The profile-scope module documents all three settings that still receive a refusal.


The locked Nix verdict at /nix/store/8bww995l0c02gg5xk881qyyc0z51c3z8-belay-verdict
covers 7,868 records in 59 corpora. Eleven cases moved from MODEL_UNSUPPORTED
to AGREE against main (88523528478c). Corpus-v4 and corpus-v5 each gained
four, corpus-v3 gained one and the synthetic workload gained two. The other
two immediate-profile cases in v4 and four in v5 now name their remaining
restrictions: a column default expression, an UPDATE expression on a unique
key, and deferred foreign-key enforcement. No other verdict or diagnostic
changed.
