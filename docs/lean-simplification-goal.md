# Long-term Lean simplification goal

Date: 2026-10-28. Status: ACTIVE; objective accepted by the owner on this date.
Audience: designers, implementers and reviewers.
Owner request: roughly halve the Lean code while keeping at least 90% of current
functionality. This objective guides ADRs [0025][adr25], [0026][adr26] and later work.

## Objective and constraints

Reduce maintained, first-party Lean code to **at most 45,000 non-comment,
nonblank lines**, while retaining **at least 90% of the fixed capability baseline**
below and every essential capability. Preserve the semantics, mathematical
strength and trust guarantees of retained capabilities. Prefer generalization
and deletion of duplication. Public names and module boundaries may change.

45,000 is the operative threshold; "roughly halve" describes its scale.
The measured baseline is 88,030 lines, replacing the initial estimate of 87K.
ADRs 0025/0026 are the first workstreams, not evidence that they alone reach 45K.
Their current full-preservation requirements remain in force. The 90% floor
does not authorize an implementer to remove features or weaken those contracts.
Each capability loss needs an explicit owner decision and the corresponding
specification amendment before implementation. No losses are approved now.

## Fixed source baseline and counting scope

Baseline: `ad5684bb16e346310e17635832699cc7e23254c3`, the reviewed spec branch
on production main `3e2212ed6983`. Counter: **scc 3.7.0**, sum of its `Code` field.
Count tracked, first-party `.lean` files, including imports, proofs, examples,
test fixtures, Lean tooling and Lake files. Count duplicates; use no deduplication,
generated-file detection or large-file exclusion switches.

Exclude dependencies, build outputs and generated case instances. The only
tracked historical exclusions at baseline are `experiments/proof-boundaries`,
`experiments/proof-simplification` and `experiments/surface-s1`: 31 files,
1,835 code lines. These frozen experiments remain replayable. New maintained
code counts wherever it is placed, including under `experiments/`.

| Scope | Files | Code lines |
| --- | ---: | ---: |
| Model | 878 | 56,376 |
| Surface | 245 | 12,817 |
| SQL text package | 33 | 1,899 |
| Conformance package | 17 | 973 |
| Public documentation tools package | 2 | 134 |
| **All packages** | **1,175** | **72,199** |
| Test fixtures | 246 | 15,608 |
| Other Lean tooling and conformance | 2 | 223 |
| **Counted total** | **1,423** | **88,030** |

The baseline was counted in a standalone Nix derivation using the repository's
locked nixpkgs and a frozen copy of the tracked files. Its `counts.json` and
`baseline.json` retain the totals, exact revision and file list:
`/nix/store/kjhi4725xx8lwxhxpjcrx64xf2ncsz7k-lean-simplification-baseline-20261028`.
This is source-size evidence, not proof or conformance acceptance.

To recount the baseline, use a clean checkout of that exact revision and scc
3.7.0. The file list and file contents must come from the same revision:

```bash
mapfile -d '' lean_files < <(jj file list -r @ \
  -T 'path ++ "\0"' 'glob:**/*.lean ~ experiments')
test "${#lean_files[@]}" -eq 1423 || exit 1
timeout 60 scc --no-gitignore --no-ignore --no-scc-ignore \
  --format json "${lean_files[@]}"
```

The blanket `experiments` exclusion in this baseline-only command is valid
only at the recorded revision. At later milestones select all maintained files
and exclude only the frozen historical inputs above; record any scope changes.
Use the same counter and show packages and tests separately.

Embedded Lean in Python templates is outside this standalone-file metric;
generated case instances are not counted repeatedly. Moving maintained logic
into templates, generators, another language, another repository or an excluded
directory earns no reduction credit. Record transferred code separately and
include it in the goal total until equivalent maintenance work is actually
removed. Line packing, removing required documentation or dropping unique test
coverage does not satisfy the objective. The complete implementation, including
new abstractions, instances, tactics and migrated clients, determines the saving.

## Fixed capability baseline

The unit is an existing capability group, not a theorem name, test count or
percentage of all SQLite behavior. There are **30 equally weighted groups**;
success requires **at least 27 retained groups**, including the essential ones.
All scope references here mean their contents at `ad5684bb`, not later edits.

**S01–S17** are the 17 implemented rows, in order, of the baseline
[ADR17 capability inventory][surface]. Each row's entire behavior, contract and
linked acceptance evidence defines one group. S01–S04 (SQL text, databases,
programs and universal claims) and S06 (complete-execution equivalence) are
essential. Names such as `Holds.iff_selectOne_count` identify the old API;
equivalent generic derivations retain the capability without retaining the name.
Explicit deferrals in that inventory are outside the baseline.

**M01–M12** use the baseline [supported subset][subset] and [execution profiles][profiles],
including their existing restrictions and distinctions between syntax, resolution
and execution. M13 uses [ADR22][adr22] and the existing mathematical contracts
identified by ADR25/26's target inventories, not their proposed implementations.

| ID | Complete baseline capability group |
| --- | --- |
| M01 | Catalogs, table shapes, affinities, defaults, constraints, generated columns, STRICT and WITHOUT ROWID. |
| M02 | Supported CREATE/DROP/ALTER operations, renaming, DROP COLUMN and dependent-object handling. |
| M03 | INSERT VALUES/SELECT, UPDATE, DELETE, RETURNING, UPSERT and conflict algorithms. |
| M04 | Foreign-key enforcement, selected mappings, NULL behavior and supported actions. |
| M05 | Supported triggers, recursive triggering, WHEN/RAISE and triggered writes. |
| M06 | Projection, filtering, FROM-less queries, joins and merged names. |
| M07 | Aggregation, grouping, DISTINCT/HAVING, compounds, ordering and LIMIT/OFFSET alternatives. |
| M08 | Expression/correlated subqueries, derived sources, nonrecursive CTEs and views. |
| M09 | Non-JSON value operations/functions, numeric conversions, collations, text and date/time functions. |
| M10 | JSON/JSON5/JSONB, JSON sources/aggregates, subtype and fault behavior. |
| M11 | Parameters, clocks, counters, transactions, snapshots and continuing/stopping execution outcomes. |
| M12 | Supported metadata/check pragmas and connection settings. |
| M13 | Independent validity/FK atoms, conditional preservation and the model proof guarantees targeted by ADR25/26. |

A group receives one point only when its complete baseline capability remains.
A partial loss, narrower supported domain, stronger proof assumption, weaker
conclusion or missing execution quantifier receives zero. Renaming and generic
proof derivation receive full credit when the original claims remain derivable.
Unverified retention is recorded as unknown and earns no point until checked.
Record both a direct loss and any consequential losses in other groups; do not
silently count dependent capabilities as retained. New features do not offset
losses, and splitting or regrouping the baseline cannot improve the score.

Kernel trust, honest supported/unsupported boundaries and SQLite semantics for
retained behavior are mandatory regardless of score. Preserve error and output
observations, all relevant execution branches, transaction snapshots and the
actual premises of retained proofs. Existing native conformance, kernel proofs,
checked documentation and client applications establish retention. Passing tests
alone does not establish unchanged theorem strength or full group retention.

## Milestones and decisions

At substantial milestones, record the revision, package/test/other code totals,
net change including supporting abstractions, retained/unknown/lost group IDs,
essential-capability status, evidence and any owner-approved losses. Keep the
baseline denominator fixed. Counter or scope changes require a comparable
baseline recount, not a fresh budget. Temporary growth within a refactor is
allowed; measure its completed result. Source reduction implies no speedup.

| Milestone | Packages | Tests | Other | Total | Capability status and decisions |
| --- | ---: | ---: | ---: | ---: | --- |
| Baseline `ad5684bb`, 2026-10-28 | 72,199 | 15,608 | 223 | 88,030 | 30/30 by baseline definition; all essential groups present; no approved losses. Nix source count above. |
| ADR25/26 `23a3427b`, 2026-10-28 | 70,876 | 15,919 | 223 | 87,018 | Net -1,012 lines; 30/30 retained. Unknown: none. Lost: none. All essential groups retained; no approved losses. |

The ADR25/26 count uses the same Nix-pinned scc 3.7.0 executable and the same
31 byte-identical historical exclusions as the baseline. Its revision, counter
hash, 1,458 tracked Lean file hashes and totals are retained in
`/nix/store/3136rk4i9jjkxf40fmm4lfdndyjw7qaf-lean-simplification-final-20261028`.
The maintained count includes 1,427 files: 1,176 package files, 249 test files
and two other files. Packages decrease by 1,323 lines, tests increase by 311,
and other code is unchanged. No maintained implementation was transferred to
embedded templates or an excluded location; the transferred-code adjustment
is zero. The 1,012-line reduction is about 1.15%; 42,018 more lines must be
removed to reach the goal. The goal remains ACTIVE.

The final audit retains **S01–S17 and M01–M13: 30/30**. Unknown and lost groups
are empty. Essential S01, S02, S03, S04 and S06 all remain; no loss is approved.
The [combined acceptance record](../plans/20261028-proof-refactor-ci.status.md)
records final Nix full-suite, verdict, configured Nix, scheduled, documentation,
API-reference and affected-mutant acceptance. Its matched dependency report
verifies the shared proof routes and removed names. The separate CI task still
awaits hosted mutation measurements; it does not change this capability score.
The original-formula witnesses passed Nix at `53a346e1` before their redundant
copies were retired. Current unique arbitrary-limits, arbitrary-depth and
append value/fault/subtype checks remain. Passing tests alone does not establish
unchanged mathematical strength.

The fixed-group audit uses the following source and mathematical evidence,
matched to the final passing acceptance owners:

| Fixed groups | Retention evidence beyond test counts |
| --- | --- |
| S01, S12–S14, S16–S17 | SQL translation, SQL-file/freshness, cost collection, editor and checked-doc behavior keep their executable definitions. Import and native-artifact registration changes retain public instances and installed consumers. [Primitive ownership](../plans/20261028-proof-primitive-imports.status.md) and the combined Nix record cover those boundaries. |
| S02–S03, S07, S11, M01–M05, M11–M13 | The 84 original endpoint formulas and raw/surface generic formulas retain independent atoms, saved databases, actual inputs and every execution branch. Resolver fields retain their separate premises. [Preservation](../plans/20261026-preservation-context.status.md) and [resolver certification](../plans/20261028-resolver-certificate.status.md) record the accepted witnesses and lasting clients; statement/row-engine semantics are unchanged. |
| S04, S10, M06–M10 | The 45 output and 17 source formulas remain derivable; four expression proof paths share reasoning and the context laws strengthen. Complete outputs, weaker resolver transports, arbitrary depth, faults and JSON subtype remain. [Query outputs](../plans/20261028-query-output-facts.status.md), [source agreement](../plans/20261028-source-agreement.status.md) and [expression congruence](../plans/20261028-expression-congruence.status.md) record the exact boundaries; query/expression evaluators are unchanged. |
| S06, S08, S15 | Universal formula equivalences preserve all four execution relations, actual versus permitted results, branch end states and full versus scoped simulation. [Profile acceptance](../plans/20261028-execution-profiles.status.md) retains independent singleton, bind and frame premises and the migration/application clients. |
| S05, S09 | Profile proof closing and actual-run refutation changed. The existing program, NOT-IN, alias and printed-proof cases preserve promised outcomes at their unchanged budgets and kernel certification. [Profile acceptance](../plans/20261028-execution-profiles.status.md) records this scope; retention does not assert identical search heuristics. |

The [one-time Nix cost sample](../plans/20261028-expression-congruence.status.md#final-nix-proof-cost-sample)
records nine final owners and 50 definition-body nodes. It separates body
elaboration from whole-file time; there is no comparable pre-migration timing
baseline or build-speed claim. This milestone closes when its reviewed records
are integrated and published with the task completion records.

ADRs and assigned tasks link here and state their expected contribution and
capability effects. Create implementation task/status files only at assignment.
Reuse existing acceptance tools. ADR25/26's temporary migration witnesses retire
after final acceptance as specified; unique semantic, premise and trust coverage
remains. This goal adds no permanent count gate, dashboard or test framework.

[adr25]: adr-0025-compositional-preservation-proofs.md
[adr26]: adr-0026-semantic-proof-boundaries.md
[adr22]: adr-0022-database-validity.md
[surface]: ../plans/20261024-adr17-guide-acceptance.status.md#capability-inventory
[subset]: semantic-subset.md
[profiles]: execution-profile.md
