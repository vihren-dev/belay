# S5 part 1 evidence through SQL inference

Created 2026-10-24. Historical progress snapshot through commit `69cd41be`.
Earlier entries describe what was pending at that time; the current state is in
[the S5 status](20261024-surface-s5.status.md). All recorded acceptance results are Nix results.

## Progress

- 2026-10-24: specified S5 from the guide and current surface, with explicit
  certification/replay boundaries and acceptance checks. No Nix result is
  claimed. Task review, compatibility check and implementation are pending.
- 2026-10-24: task review `20261024T121144Z-0f5f579b` found no musts and three
  source-location shoulds. The task now identifies the guide and S4 specification
  by path and commit, and links the recorded owner check-cadence instruction.
  Compatibility and implementation remain pending.
- 2026-10-24: follow-up review `20261024T121311Z-4a2fcd90` found no musts and
  one source-access should. Replaced workspace-only citations with repository
  names and file paths; added a pinned guide link. The task restates the required
  S5 behavior and names the S4 dependency; S4's referenced source is still local.
- 2026-10-24: review `20261024T121740Z-f2681d23` found no musts and one should.
  The task now also marks the S4 source commit as not yet pushed. It must be
  replaced with the final S4 revision when implementation starts.
- 2026-10-24: removed the direct private-repository link to respect the product
  repository's publication boundary; the source path/revision remain recorded.
  Clarified that S4 checks both actual raw `oneOf` continuations and all concrete
  `rows` continuations. A raw Lean continuation failure must not be reported as
  a native SQLite statement failure. Final S4 names still wait for its review.
- Read-only preflight against final S4 work found a direct certification path:
  `Sql.decidableSucceedsFrom`, `Succeeds.not_of_failure`, and `Succeeds.send_iff`
  cover concrete failed runs under complete environments. No new S4 API is needed.
  Candidate expressions must pass kernel checking and a transitive axiom audit:
  `DbBang` can return synthetic sorry on its error path. `Script` retains bound
  values and syntax, but original SQL text/ranges require elaboration metadata.
  Plausible v4.34.0's shrinking hook has no decreasing-size proof, so budget,
  cancellation and recertification must also cover shrinking. Use sampling hooks,
  never its admitting tactic. This is source inspection only; compatibility,
  replay, editor behavior and implementation acceptance remain unverified.

- 2026-10-24: updated the task and its source citations together immediately
  before the implementation handoff to `s4_part1`. S4 is DONE and published in
  PR #244, with checked source `24ca8b4c` and completion `70705018`.
  Its 865 full tests, 70 Nix checks, 47 scheduled checks, verdict and unchanged
  predictions pass; both email extracts and balance pass the installed runtime.
  The task now names the final success and certification interfaces explicitly.
  The guide's S5 sections were rechecked at the published private guide source.
  Read-only dependency inspection resolves Plausible v4.34.0 to
  `118aa17ee84656b8bd727fef7c458ee8c833385c`; compatibility under Lean 4.34.1
  still needs a build. No dependency or implementation change is claimed here.

- 2026-10-24: handoff review `20261024T193314Z-fa783845` found no musts
  and one stale-status should. Updated the prerequisite paragraph to published
  PR #244 and assigned implementation to `s4_part1` in an isolated workspace.
  Compatibility and implementation checks remain pending.

## Implementation workspace

- Assigned workspace: `sqlite-verifier-s5-counterexamples`, based on published
  `0569149b2b9695d4aa59608522734482dff3e8fe`. Carried only this task/status and
  handoff review records from `e50e1f9e`; no other planning history is merged.
- Work follows the three task parts: samplers and explicit certified witnesses;
  shared bounded search and the check command; automatic checks and editor
  regression actions. Each part retains its full acceptance requirements.
- Own new surface sampling, candidate, certification, replay, check and refute
  modules and fixtures. Shared barrel, Lake, Nix dependency and manifest changes
  are limited to those entries and coordinated with the source/FK agents.
- The shell configuration matches the authorized ADR17 workspace. Shell access
  is enabled. Both heavy build slots are occupied by other tasks; compatibility
  and package builds await a slot. Targeted handoff check: `tests/docs_test.py`.
- Carry review `20261024T193903Z-2299647d` found no musts and one stale-header
  should. The task header now records assigned implementation after the completed
  handoff review. The scope and acceptance requirements are unchanged.
- Handoff-header follow-up `a697544855ae497dff5b2adba0bdd6681284c11f`
  passed review `20261024T194046Z-a6975448` with no findings.
- Plausible compatibility passes in Nix at
  `/nix/store/abjwwyn18b381n5yla92lhk8ncjpbdgr-plausible-0.1.0`.
  The pinned source is `118aa17ee84656b8bd727fef7c458ee8c833385c`, built by
  the repository's Lean 4.34.1 compiler, selecting only `Plausible` and
  `Plausible:shared`. The dependency has no requirements, and its tests are not
  selected. `build-support/plausible.nix` reuses the existing package builder.
  Surface wiring and candidate/certification checks remain in progress.
  Targeted configuration checks: `tests/surface_layers_test.py` and
  `tests/docs_test.py`. No model, runner or lock input changes are intended.

- First explicit-witness unit: `CounterexampleCertificate` checks the exact
  proposition with the kernel and audits used declarations, types, opaque bodies
  and local assumptions transitively. It rejects admitted, native-decision,
  excluded and user-axiom evidence. Kernel checking also rejects unsafe inputs.
  `CounterexampleWitness` exposes arbitrary selectors and a database/environment
  convenience record; `SqlRefute` supplies the explicit tactic form. Preconditions
  and complete environments are proved, never assumed. Fixed-state decisions use
  S4's existing instances, including actual and concrete `oneOf` continuations.
- The focused Nix surface gate passes 11 checks at
  `/nix/store/c0y601j2xvw2rjnh8a7c373wymw91ava-sqlite-verifier-test-explicit-witness-1`.
  It selects `counterexample or surface_layers` from the actual surface suite.
  The installed surface is
  `/nix/store/x5rfddfpg6jbdqsbpac1kdl7ivizx1l3-belay-0.1.0`.
  Six refutations have only the standard logical axioms. Fixtures also reject
  incorrect propositions, direct/indirect unsafe proofs, admitted and invalid
  databases, excluded declarations/locals, false preconditions and incomplete
  environments. The dependency checks keep Plausible outside the model, text
  package and runner. Targeted source checks: `tests/docs_test.py` and
  `tests/surface_layers_test.py`; package cadence: `just dev-build`.
- The Nix surface maps the exact pinned Plausible Git dependency to its supplied
  local output before Lake loads it. The package builder makes a copied subject
  writable before inserting nested requirements; existing nonnested package
  build scripts are unchanged. The model output remains
  `/nix/store/8kpj38jvlfpq210wa4wdn76w33vggdxc-belay-sqlite-model-0.1.0`.
  Review `20261024T194521Z-c8b305ee` had no musts and one comment-placement should,
  now fixed. Part 1 remains OPEN until sampling and its acceptance gates pass.
  Source-only sampler work uses the temporary `s5-sampling` workspace while this
  unit's checks and independent review run.

- Explicit-witness review `20261024T200819Z-3681ede5` found no musts and one
  naming should. The permitted logical axioms and native-decision name prefix
  are now named, documented policy values. The repeated focused Nix gate passes
  11 checks (60 deselected) at
  `/nix/store/xmc2w3gqgxwyhjiv4hk136yxdfklixfd-sqlite-verifier-test-explicit-witness-1`,
  including the malicious-evidence and dependency-boundary fixtures. Its surface
  output is `/nix/store/kmb2pjmnllayqavkjr429r9qrz06g16q-belay-0.1.0`.
  Targeted checks remain `surface_counterexample_test.py`,
  `surface_layers_test.py` and `docs_test.py`; package cadence is `just dev-build`.
  Sampling and all later task outcomes remain OPEN.

- Certificate policy follow-up `765049777e8bd922661d5dbb10365d2f40a03df5`
  passed review `20261024T202011Z-76504977` with no findings.
- Shared sampler unit: `SampleValues`, `SampleDatabases` and `SampleShrink`
  expose Plausible generators/instances, deterministic seeds, explicit schemas,
  stable targeted SQL values, row bounds and validity-preserving shrink proposals.
  A rejected generated candidate returns a generator error; it cannot return a
  supplied base that exceeds the row bound. `CounterexampleShrink` counts every
  attempted proposal and kernel-certifies every retained refutation. A custom
  shrinker that repeats its input still reaches the finite attempt limit.
- The focused Nix surface gate passes 12 checks (60 deselected) at
  `/nix/store/99b0g2wgmldn0qxsjjc4fsdw7fw15dwc-sqlite-verifier-test-sampling-1`.
  The sampler fixture certifies generated/shrunk validity and exact NOCASE,
  non-ASCII and SUM-overflow examples under their concrete schema/row premises.
  It also rejects invalid/nonrefuting shrinks and checks a repeating shrinker
  and a constrained base larger than the requested row bound. The existing
  certificate and layer fixtures pass in the same installed runtime.
  Targeted checks: `surface_sampling_test.py`, `surface_counterexample_test.py`,
  `surface_layers_test.py` and `docs_test.py`; package cadence: `just dev-build`.
- That installed run exposed the surface test helper's incomplete module setup
  for Plausible's Lean module-mode files. It now supplies server/private data
  and IR signature/body artifacts in the groups used by Lake's setup output.
  The production package was unchanged for the passing retry. SQL schema-hint
  extraction is source-only work in the temporary workspace; part 1 and the
  task remain OPEN. Replay, shared search and automatic/editor checks follow.

- Sampler commit `593caf88cb5c3424813c54b21d4164ad4da564e4` passed review
  `20261024T203050Z-593caf88` with no musts and one module-purpose should.
  Added the four purpose docstrings and recorded the resolution.
- SQL inference now collects source/column names, literal values and actual
  bindings through `SampleHints`, `SampleQueryHints` and `SampleScriptHints`.
  Its empty/inferred-schema candidates use the existing targeted sampler. These
  are guesses only; explicit schemas and generators remain available, and the
  original claim's preconditions and refutation still need kernel certificates.
- The focused Nix gate passes 13 checks (60 deselected) at
  `/nix/store/x3882h15iq2yzajk98pmn1hzr6cmrv31-sqlite-verifier-test-inference-1`.
  It covers quoted names, aliases, parameters, DML constants, and a NOCASE data
  witness under exact schema/row premises, together with sampling and certificate
  regressions. The primitive now checks the Database/Env types even for unused
  witness fields; two wrong-type candidates are rejected. Targeted checks include
  `surface_inference_test.py`, the prior sampler/certificate/layer fixtures and
  `docs_test.py`; package cadence is `just dev-build`. The final docstring wording
  identifies which DDL forms add hints; executable definitions are unchanged.
  Part 1 remains OPEN through replay and its full/verdict acceptance.
