# Replace specialized preservation endpoints with generic applications

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Specification: [ADR 0025 D1 and D4](../docs/adr-0025-compositional-preservation-proofs.md).
Record: [status](20261026-preservation-api.status.md).
Present problem: the owner requested removal of the per-atom endpoint matrix;
the [inventory](../experiments/proof-simplification/inventory.json) identifies
84 concrete specializations over existing general proofs.

## Required behavior

Library clients can derive every inventoried claim with its existing hypotheses
using generic preservation laws and per-invariant evidence. The 84 inventoried
specializations are removed from production source and all callers are updated.
Their six pure-wrapper modules disappear from imports, Lake roots and exports.
The inventory records the frozen baseline; reconcile names against the current
integration revision before editing. Report any semantic drift explicitly.

Per-atom condition aliases and key-specific effect/state/outcome predicates
whose definitions duplicate generic applications are removed where replaced.
No aliases preserve replaced public names. Keep distinct semantic conditions,
per-atom preservation evidence, the generic `runScriptFrom_admittedWith`, and
the used `runScriptFrom_valid`/`runScriptStep_valid` bundled helpers.

Model examples, surface callers and checked documentation use the resulting
API. The conditions remain visible and usable with raw resolved statements.
The API does not require `Database.Valid` when a smaller independent property
was sufficient before. General conjunction composition remains available.

## Acceptance checks

- The old formula suite is restated through generic applications, covering all
  removed endpoints. Anonymous examples or test-local declarations may carry
  the formulas; they are not replacement public endpoint aliases. Their
  assumptions and conclusions are compared with the frozen inventory source.
- Compile the affected model examples and formula suites in Nix. Audit the
  new proof closures under the existing standard-axiom policy. Retain native
  necessity examples and transaction/failure examples; deleting names must
  not delete their semantic coverage.
- Verify both conditional raw runs and resolver-derived surface runs, including
  support-independent NOT NULL/type/CHECK claims, admitted dependencies and
  fixed/selected FK mapping claims. The experiment's 11 representative formulas
  establish feasibility; they do not replace complete migration coverage.
- The model, text package, surface and conformance package build. Public docs
  and API-reference checks pass with no stale declaration references. Existing
  surface `Database.Valid` program guarantees continue to compile.
- No replaced production declaration, module import or Lake root remains.
  Retained historical evidence is explicitly outside that deletion check.
  Report actual net declaration/module/line changes; do not claim build-speed
  gains from source deletion alone.

Relevant existing suites include `valid_atoms_theorems_test.py`,
`keys_unique_theorems_test.py`, `admitted_atoms_run_theorems_test.py` and the
foreign-key theorem suites under `tests/`. The three named formula suites
currently run as host-owned checks through `just test-source`, using Nix-built
libraries. Register their migrated checks in the existing `model` Nix suite
in `tests/nix_suites.json`, including only needed helper/fixture inputs.
`shared_table_shape_test.py`, which supplies `compile_checks`, is already in
that suite. Broader test-ownership cleanup is outside scope.
The admitted-run suite constructs names from `ATOMS` and three run prefixes;
a literal-name search alone does not find all affected consumers.
All subprocess checks retain configured timeouts. Apply the repository check
cadence at implementation commits and completion; there is no new CI framework.

## Tricky points and boundaries

`RunHolds`, `RunHoldsReady`, `ScriptRunHolds` and `ScriptRunDerived` already
supply the lifting. `ProgramRun` and `ProgramLaws` use the bundled valid helpers.
Some surface claims need admission and execution-mode/matching-limit premises
to derive conditions. These facts must not be replaced with unexplained lambdas
repeated at many callers: retain a reusable resolver bridge where it is needed.

Changing statement/run execution, atom definitions, FK action semantics, judge
inputs, corpus expectations, or unrelated resolver proofs is outside this task.
The foundations task supplies the lower generic predicates needed to replace
the key-specific aliases without an import cycle. Integrate that boundary
before completing this task. The execution-condition task uses the resulting
generic names; its interface changes must retain these migrated formulas.
