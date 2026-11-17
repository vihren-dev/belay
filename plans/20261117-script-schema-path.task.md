# Schema states along a successful script

Created 2026-11-17. Issue [#411](https://github.com/vihren-dev/belay/issues/411).
Status: open.

Given the initial catalog, saved catalog and settings, resolution determines
the resolved statements and the resolution state at each script position.
For every execution of a continuing step with a non-error output, its next
connection has the resolution state that the resolver returned. This also
holds for the other executions of INSERT from SELECT. A caller that follows
the path on a branch of sendStatements can use its intermediate resolution
equations and conclude that a complete branch with only successful outputs
ends with the final resolution state. A failing statement gives no guarantee
about its next catalog.

The example in examples/table-rebuild/Proof must use the computed path in
both the preservation and the success proof. The caller establishes the
initial schema and the resolution of the script once. It can still carry
row-dependent facts alongside the path. The sample database's execution
is unnecessary for computing intermediate catalogs.

## Acceptance

The kernel checks the public step and script laws, including arbitrary
executions of INSERT from SELECT. The README rebuild proofs compile against
the laws with their existing hypotheses and conclusions. Remove the
per-statement proofs of catalog, snapshot and setting agreement that the
path discharges. Record the change in example proof length. Run the
repository checks for the model, public declarations and rebuild example.

## Existing laws

ScriptRunLaws.lean relates the model's own run to resolveFrom. The latter
returns resolved statements and the final state. ResolveState.after describes
each transition. ExecutionEffects.lean accounts for all executions of an
ordinary step. SendStatementsInvariant.lean and SendStatementsSuccess.lean
carry a property indexed by script position. Transaction control and
connection settings have separate step laws.
