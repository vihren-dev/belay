# Replace specialized preservation endpoints with generic applications

Date: 2026-10-26. Status: IN PROGRESS; assigned 2026-10-28.
Audience: the implementation team.
Specification: [ADR 0025 D1 and D4](../docs/adr-0025-compositional-preservation-proofs.md).
Record: [status](20261026-preservation-api.status.md).
Targets: [endpoint, predicate and caller inventory](../docs/spec-preservation-api-targets.md).
Present problem: the owner requested removal of the per-atom endpoint matrix.
The target inventory identifies 84 specializations at `3e2212ed6983`, reviewed
2026-10-28. The [experiment inventory](../experiments/proof-simplification/inventory.json)
is historical: its 18 surface names now have the prefix `runScriptAllFrom_`.

## Required behavior

Library clients can derive every inventoried claim with its existing hypotheses
using generic preservation laws and per-invariant evidence. The 84 inventoried
specializations are removed from production source and all callers are updated.
Their six pure-wrapper modules disappear from imports, Lake roots and exports.
The target tables govern current names and formulas. The surface claims now
cover every complete execution, including alternative INSERT-query executions;
preserve that stronger guarantee. Report later semantic drift explicitly.

Per-atom condition aliases and key-specific effect/state/outcome predicates
whose definitions duplicate generic applications are removed where replaced.
No aliases preserve replaced public names. Keep distinct semantic conditions,
per-atom preservation evidence, the generic `runScriptAllFrom_admittedWith`, and
the used `runScriptAllFrom_valid`/`runScriptStep_valid` bundled helpers. The last
helper covers every execution of a step, not only its canonical next connection.

Model examples, surface callers and checked documentation use the resulting
API. The conditions remain visible and usable with raw resolved statements.
The API does not require `Database.Valid` when a smaller independent property
was sufficient before. General conjunction composition remains available.
Current FK conditions require selected-parent equality for rename, because
`sameOutline` does not imply it. DROP COLUMN uses execution checks and adds no
extra FK atom condition. Preserve these latest formulas rather than recovering
an obsolete unconditional rename claim from the historical baseline.

## Acceptance checks

- The old formula suite is restated through generic applications, covering all
  removed endpoints. Anonymous examples or test-local declarations may carry
  the formulas as temporary migration witnesses. Compare their assumptions and
  conclusions with production revision `3e2212ed6983`. The historical experiment
  remains replayable at its old revision; it does not validate the stronger
  current all-execution formulas.
- Compile the affected model examples and formula suites in Nix. Audit the
  generic proofs and independently proved invariant evidence under the existing
  standard-axiom policy. Retain native necessity examples and transaction/failure
  examples; deleting names must
  not delete their semantic coverage.
- Verify both conditional raw runs and resolver-derived all-execution surface runs, including
  support-independent NOT NULL/type/CHECK claims, admitted dependencies and
  fixed/selected FK mapping claims. The experiment's 11 representative formulas
  establish historical feasibility; they do not replace complete current
  migration coverage. Preserve canonical-run claims via their membership in
  complete executions without weakening the surface claims to that one run.
  Reuse current rename and DROP COLUMN evidence; these cases do not enlarge the
  84-endpoint removal list or require another per-atom test matrix.
- The model, text package, surface and conformance package build. Public docs
  and API-reference checks pass with no stale declaration references. Existing
  surface `Database.Valid` program guarantees continue to compile.
- No replaced production declaration, module import or Lake root remains.
  Retained historical evidence is explicitly outside that deletion check.
  Report actual net declaration/module/line changes; do not claim build-speed
  gains from source deletion alone.

Relevant existing suites include `valid_atoms_theorems_test.py`,
`keys_unique_theorems_test.py`, `admitted_atoms_run_theorems_test.py` and the
foreign-key theorem suites under `tests/`. The valid-atoms formula suite runs in the existing `model` Nix suite and
compiles the four temporary `PreservationApiWitnesses*.lean` files until the
execution-condition task's final Nix acceptance. The other two named formula suites remain host-owned
checks through `just test-source`, using Nix-built libraries. Only lasting checks of current contracts remain registered in the
existing `model` Nix suite in `tests/nix_suites.json` after retirement, with
needed helper/fixture inputs. Temporary checks can use the existing Nix harness
during migration.
The exhaustive retired-endpoint matrix is temporary; Nix acceptance does not
require registering it as a permanent suite.
`shared_table_shape_test.py`, which supplies `compile_checks`, is already in
that suite. Broader test-ownership cleanup is outside scope.
The admitted-run suite constructs names from `ATOMS` and three run prefixes;
a literal-name search alone does not find all affected consumers.
All subprocess checks retain configured timeouts. Apply the repository check
cadence at implementation commits and completion; there is no new CI framework.

## Test lifetime

Apply ADR 0025 D4's retirement rule. Share the temporary formula witnesses with
the execution-condition task through the final contract change. Record Nix
acceptance at that revision, then remove redundant sources and registrations
before refactor completion. Keep focused premise-strength checks, actual
clients and semantic counterexamples; avoid an invariant-by-executor matrix.
Do not remove mixed test files wholesale: unique lookup, whole-statement atom
guarantees and the used Valid helper/definition checks can remain meaningful.
Historical formula witnesses are replayed at their recorded revision. Record
which lasting coverage replaces them in the existing status; no new registry
or test runner is needed.

## Tricky points and boundaries

`RunHolds`, `RunHoldsReady`, `ScriptRunHolds` and `ScriptRunDerived` already
supply the lifting. `ScriptConditions` owns the all-branch condition predicate;
`InsertSelectKeeps` lifts own-run evidence to every `StatementRun.effects` member.
`ProgramRun` and `ProgramLaws` use the bundled valid helpers.
Some surface claims need admission and execution-mode/matching-limit premises
to derive conditions. These facts must not be replaced with unexplained lambdas
repeated at many callers: retain a reusable resolver bridge where it is needed.

Changing statement/run execution, atom definitions, FK action semantics, judge
inputs, corpus expectations, or unrelated resolver proofs is outside this task.
The foundations task supplies the lower generic predicates needed to replace
the key-specific aliases without an import cycle. Integrate that boundary
before completing this task. The execution-condition task uses the resulting
generic names; its interface changes must re-establish the affected formulas
before their shared temporary witnesses are retired.
