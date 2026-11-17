# Status of named SQL claims

Created 2026-11-17. Open. [Task](20261117-named-check-claims.task.md).

Tooling/Counterexamples/CheckAutoProof.lean selects the proof route after
Programs/Automation/CheckAutoProof.lean opens the claim. The existing
SelectCheckCases.lean defines selectClaim but calls the checker on its body.
Implementation, the named examples, and the repository checks are pending.
