# Exact steps for plain UPDATE and DELETE

Created 2026-11-24. Status DONE. Audience: implementers and reviewers.

Slice 2 of [ADR 0033](../docs/adr/adr-0033-exact-step-rules.md) covers UPDATE
and DELETE with any subquery list, no RETURNING columns and no write rules.
Given only a resolution to either kind, a client can read the complete step
from its registered equation. The clock and first unknown counter take
precedence over table lookup. The equation states which readiness checks end
the run, the output and counts of each continuing case, the next connection
and its further executions. Plain UPDATE can fail with a datatype mismatch or a constraint violation.
Plain DELETE has no SQL error after its support checks pass.

Clients use the same projections, send rule and tactic path as the pilot.
Proofs use the kind rules wherever D8 applies. The two plain database-effect
laws, the two kind-specific send rules and their two ifOk rules are replaced.
Rules about all RETURNING lists or write-rule modes have a wider domain.
The statement interpreter and the verdict it computes retain their meaning.

## Acceptance

Lean checks the original statements of all removed laws as retention
witnesses, including their original premises. Surface fixtures prove claims
over a variable database for both kinds, covering an UPDATE failure or every
UPDATE input. Their proofs use public rules without naming the step,
resolution or statement-run functions. The existing public proofs in the
S6 automation, send-rule and SELECT suites still compile. The registered
rules and their callers pass the package builds, documentation inventory,
full suite and locked verdict. The verdict files match the starting revision.
The status record identifies changed proofs, capability coverage, fixture
elaboration times and code counts as specified in D11.

## Code boundaries

The branches in Schema/Dispatch/StatementStep.lean compute the effect and
counts. Programs/Scripts/PlainInsertRule.lean shows how a rule exposes
the clock, counter and table checks. The two PlainUpdateEffect and
PlainDeleteEffect modules in the model also contain results about more
general writes. On the surface, SqlRunRules and SqlRunGoals route sends and
name the hypotheses. The S6RulesEffects, S6AutoEffects, S6AutoPaths and
PurgeFrameClaims fixtures exercise those paths. Retention witnesses may use
a general rule for a send until their final acceptance under D12.
