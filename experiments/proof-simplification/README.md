# Preservation proof simplification experiments

Date: 2026-10-26. Status: CHECKED IN NIX AT THE RECORDED REVISION.
Audience: designers and reviewers.
Base: integration commit `6413afe3ff50` in the isolated workspace
`/home/codex/work/sqlite-verifier-proof-simplification`.
Specification: [ADR 0025](../../docs/adr-0025-compositional-preservation-proofs.md).
Acceptance record: [design status](../../plans/20261026-proof-simplification-design.status.md).

Rebase note, 2026-10-28: current specifications target `3e2212ed`. These
unchanged prototypes predate RENAME, INSERT SELECT, DROP COLUMN and all-execution preservation.
Their names, formulas and source-span inventory are historical. Replay this
experiment at accepted design revision `0cadcde9`; do not run it against the
rebased checkout and treat its result as current acceptance. The live target
inventory is [here](../../docs/spec-preservation-api-targets.md).

## What the experiments establish

| Experiment | Checked result | Limit |
| --- | --- | --- |
| `ApiResolved`, `ApiSurface` | 11 existing claims follow from current generic rules | Representative coverage; all 84 removals still need migration checks |
| `DispatchStatements` | Two complete statement formulas follow from the existing table-atom dispatcher | Production module relocation is not performed |
| `DispatchPrimitives` | Four old primitive formulas follow from existing general facts | Does not generalize unique-key schema or FK engine proofs |
| `ContextCore` | One raw-run induction derives both old generic formulas | Old-condition adapters are experiment evidence, not production APIs |
| `ContextSurface`, `ContextSurfaceFormulas` | One surface induction derives both old generic formulas | Production callers still need migration |
| `ContextLaws` | Conjunction, stopped suffixes and the extra state counter check retain their meanings | Broad execution tests remain implementation gates |

At the accepted revision, eight Lean files compiled against its pinned model
and toolchain. The check audits 30 named proof closures and accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Other helper proofs are
covered when they occur in those closures. Compiler warnings and missing axiom
reports fail the check. Each file has a 90-second compilation deadline.

The API equality examples compare the old and proposed mathematical function
types modulo definitional equality. They do not preserve implicit/explicit
argument syntax or the old names. This API change does not require that syntax.

## Measured opportunities

The [inventory](inventory.json) records 54 run wrappers and 30 statement wrappers.
Their declaration and docstring spans total 937 lines. Six pure-wrapper modules
total 664 full-file lines, overlapping the 937. The Nix check verifies each
recorded declaration span against the model source used by the proof experiment
and emits the counts. It does not prove that all callers migrate successfully.

The two original whole-statement declarations total 139 lines. Their experimental
replacements total 39 lines, plus a four-line evidence adapter. Their proof bodies
total 129 and 29 lines respectively. [Dispatch findings](DispatchFindings.md)
give the counting convention and a reproduction snippet. This measures source
repetition, not elaboration cost or the size of kernel proof terms.

Detailed findings:

- [API inventory, consumers and superseded obligations](ApiFindings.md).
- [Shared dispatch, primitive reuse and import boundaries](DispatchFindings.md).
- [Execution conditions and surface invariant obligations](ContextDesign.md).

## Reproduce

From a checkout of `0cadcde9`, with the repository's Nix configuration:

```sh
timeout --foreground 600 nix-build experiments/proof-simplification/default.nix \
  --out-link /tmp/proof-simplification-experiments \
  --option max-jobs 1 --option cores 2 \
  --extra-experimental-features 'nix-command flakes'
```

The result contains `results.json`, `inventory-counts.json`, one compiler log
per module, and the exact model/toolchain paths. The task status records the
accepted result path. Nix selects the current checkout's model sources, not a
developer's `.lake` cache. Local Lean runs are diagnostics only.

The target is an explicit design experiment. It adds no CI suite, production
dependency, executable behavior, claim, corpus or judge-lock change. Historical
experiment inputs can remain for replay when their old production APIs are
removed; replay them from this design revision rather than expecting the old
imports to compile against a changed API.

## Design consequences

Use existing preservation evidence and generic execution laws to replace the
endpoint matrix. Move general contracts below their specialized consumers where
the current imports prevent reuse. Let the statement condition inspect the
actual execution inputs, and keep one preservation induction per executor.

The unconditional claims keep their original strength. Readiness, matching
limits, width/catalog dependencies, FK mapping and row/schema distinctions,
partial FAIL, and transaction snapshots remain explicit. None of these
experiments justifies a weaker guarantee or an executable semantics change.

No net repository deletion or compile-speed improvement has been measured.
The implementation tasks require complete caller migration, relevant Nix gates,
and actual net counts before reporting those results.
