# Shared proof boundary experiments

Date: 2026-10-26. Audience: designers and reviewers.
Task: [experiment and design scope](../../plans/20261026-proof-boundaries-design.task.md).
Decision: [ADR 0026](../../docs/adr-0026-semantic-proof-boundaries.md).

## Result

The prototypes identify useful common semantic facts, and one abstraction to
defer. They change no production code. They demonstrate shared reasoning and
retained formulas, not a completed migration or measured build-speed improvement.

| Candidate | Decision | What the compiled prototype establishes |
| --- | --- | --- |
| Query outputs | Adopt | Exact output semantics; original count/aggregate formulas and one surface count application |
| Current/initial sources | Adopt | One agreement chain recovers both origin families and handles fixed pragmas |
| Resolver | Adopt | One statement dispatch supplies three differently conditional facts and applied-catalog validity |
| Execution observations | Adopt | One profile construction, transport and singleton argument serve four original relations |
| Expression equality | Narrow | One induction preserves value, fault and JSON subtype; two old exclusions are unnecessary |
| Primitive/import ownership | Adopt demonstrated scope | Four generic facts avoid their feature owners; three unchanged surface bodies compile with narrower imports |
| Row-engine interface | Defer | Broad and narrow contracts compile, but their obligations add complexity around compact callers |

The recurring cause is proving each projection before exposing the shared
semantic result. Another cause is putting reusable definitions beside specialized
proofs, making the import graph point in the wrong direction. Shared source and
expression agreement address repeated dependency assumptions. The row experiment
shows that similar control flow alone does not justify a common interface.

## Reproduce

Run from the repository root in its approved development shell:

```sh
timeout --foreground 600 nix-build experiments/proof-boundaries/default.nix \
  --out-link /tmp/proof-boundaries-experiments \
  --option sandbox true --option sandbox-fallback false \
  --option max-jobs 1 --option cores 2 \
  --extra-experimental-features 'nix-command flakes'
```

For this workspace, the already approved shell was supplied by
`direnv exec /home/codex/work/sqlite-verifier-proof-simplification`.
No new dev-shell authorization or production build integration was needed.
The pinned production source is report revision `3fe5caef`; prior ADR 0025
design revision `0cadcde9` is also present. The standalone derivation uses the
unchanged production package builders and the experiment sources.

## Accepted evidence

Final Nix output:
`/nix/store/sr7akfqnx2ry220gsis4v74dnm9y5vnr-proof-boundaries-experiments`.

- All 22 prototype modules compile warning-free under pinned Lean 4.34.1.
- A generated combined module imports all prototypes together successfully.
- All 70 explicitly requested proof-closure audits use only `propext`,
  `Classical.choice` and `Quot.sound`, or no axioms. These closures include the
  shared proofs and formula applications. `proofs.json` lists the exact scope.
- Baseline and narrowed copies of all three surface modules compile with their
  complete unchanged bodies. This is six further compilation checks.
- Selected-project import closures decrease from 580 to 75 for `Values`,
  580 to 142 for `Script`, and 580 to 148 for `ValueDisplay`.
- The derivation retains compiler logs, the exact surface source copies,
  `imports.json`, and model/surface/toolchain paths. Each compiler subprocess
  has a 120-second timeout. Compiler warnings, errors and unexpected axioms
  fail the check.

Nix reused the unchanged production packages. These experiments have no new
production runtime or CI dependency. Existing whole-repository acceptance and
independent review records are recorded in the task's
[status](../../plans/20261026-proof-boundaries-design.status.md).

## Detailed evidence and limits

- [Query and execution observations](query-observation-findings.md): 42 query
  endpoints are the migration scope, not 42 proven redundancies. Five query
  families remain unprototyped. The output retains possible results and errors.
- [Source and expression agreement](source-expression-findings.md): fourteen
  mirrored source stages and four equality inductions share their reasoning.
  Expression locality does not imply fault-freedom or calmness.
- [Resolver and imports](resolver-import-findings.md): three dispatches become
  one while assumptions remain distinct. Definitions must move below consumers
  to avoid cycles. Downstream production import migration is still required.
- [Row engine](row-engine-findings.md): the broad prototype is 276 physical
  lines versus 209 for its original pair; the narrow prototype is 124 versus
  82 for the original four endpoint/doc spans. These include different source
  boundaries described in the findings, not a measured production delta.

No prototype calls a replaced endpoint to establish its common reasoning.
Some use lower definitions and helper facts currently co-owned with endpoints;
the implementation specifications require their acyclic relocation. Formula
applications are experiment witnesses, not proposed compatibility aliases.
Compiled references do not capture every simp registration, source export or
anonymous test; source inspections and full affected-package compilation remain
implementation obligations.

## Specifications

[ADR 0026](../../docs/adr-0026-semantic-proof-boundaries.md) records the decisions.
Its outcome specifications cover [observations](../../docs/spec-proof-observations.md),
[agreement](../../docs/spec-proof-agreement.md) and
[foundations](../../docs/spec-proof-foundations.md).
They preserve original formulas, require caller migration and deletion of
replaced APIs, and distinguish proven generalization from remaining work.
Implementation task/status files are deferred until assignment.
