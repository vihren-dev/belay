# Proof simplification design status

Date: 2026-10-26. Status: IN PROGRESS. Audience: the implementation team.
Task: [design task](20261026-proof-simplification-design.task.md).
Base: integration commit `6413afe3ff50`.
Workspace: `/home/codex/work/sqlite-verifier-proof-simplification`.

## Progress

- Created an isolated jj workspace for experiments and specifications.
- Read the governing ADR 0022, repository rules, and relevant proof families.
- The owner authorizes replacing public theorem contracts; there are no users
  requiring compatibility aliases. Mathematical guarantees remain explicit.
- Implementation of production refactors has not started.
- The initial task review found no must findings and one wording issue. The
  task now labels its status-file link as a record to avoid two status headings.
- Prepared proposed ADR 0025 and three implementation tasks with status files:
  endpoint removal, proof foundations/dispatch, and execution-aware conditions.
  The owner requested these specifications before implementation assignment.
- The three experiment authors independently checked the relevant draft specs.
  Clarified the combined line counts, generated test consumers, stopped-step
  conditions, and the distinction from the surface fresh-run helper API.
- The source diff contains no changes under production packages, tests,
  build-support, conformance, judge or integrity. Experiments have their own
  explicit Nix target and do not add a CI suite.

## Acceptance evidence

The final experiment target passed in Nix on 2026-10-26:

```sh
timeout --foreground 600 nix-build experiments/proof-simplification/default.nix \
  --out-link /tmp/proof-simplification-experiments \
  --option max-jobs 1 --option cores 2 \
  --extra-experimental-features 'nix-command flakes'
```

- Result: `/nix/store/qcwkhrakx7wn66r217vbpcb4jc7awyhv-proof-simplification-experiments`.
- Model: `/nix/store/7h8d6sdchyp362kxx90l4iv80fgvn3lw-belay-sqlite-model-0.1.0`.
- Eight Lean modules compiled; 30 named proof closures use only the existing
  standard axiom set. The output retains every compiler log and axiom list.
- `inventory-counts.json` verifies 54 run wrappers, 30 statement wrappers,
  937 declaration/docstring span lines and 664 overlapping full-module lines.
- This proves representative API reuse, two shared-dispatch claims, four
  primitive applications, both pairs of generic run formulas and boundary
  laws. It does not certify complete production migration or build-speed gains.

The initial scope commit and its wording correction have completed Claude
reviews. The experiment/specification commit is ready for its required Claude
review. Final review records and task completion will be recorded below.
