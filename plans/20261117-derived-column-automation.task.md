# Automatic proofs for a derived-column migration

Created 2026-11-17. Issue [#404](https://github.com/vihren-dev/belay/issues/404).
Status: DONE.

On the guide's shop schema, both sql_auto and #sql_check prove that
addEmailLower succeeds and preserves the named-column customer read.
They also prove preservation of the parameterized customer lookup for
every email. The checker suggests a script that the user can run on the
original claim. Each proof must pass the ordinary certification checks.

The cost of trying these laws belongs to the existing budget. Unrelated
claims must bypass catalog evaluation. A check that returns false for a
candidate law lets the existing search continue. In particular SELECT *
changes on the shop schema and must retain its counterexample.

The laws in DerivedColumnSchema.lean and DerivedColumnSuccessCheck.lean
apply to the whole claim before the general search introduces binders.
The parameterized law needs a sample value and a proof that all parameter
values give the same statement syntax. CheckAutoProof.lean currently opens
fresh triples and restricts the general search to program and query goals.

## Acceptance

Exercise both commands on the three claims in DerivedColumnOnSchema.lean.
Re-elaborate the checker's proposed scripts. Check that the wider SELECT *
read still has a replayable counterexample and that a schema or program
outside the recognized form retains its existing response. Run the
affected surface tests and the repository review and slice checks.
