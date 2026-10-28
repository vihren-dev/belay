# Query output task status

Date: 2026-10-28. Status: IN PROGRESS; implementation awaiting combined Nix acceptance.
Audience: the implementation team.
Task: [generalize query output proofs](20261028-query-output-facts.task.md).
Specification: [ADR 0026 D1](../docs/adr-0026-semantic-proof-boundaries.md).
Assignment source: `a3dd5a9a`, after expression-congruence integration.

## Assignment audit

The expression-congruence worker inspected the current endpoint signatures,
actual consumers and test owners. All 45 target statements match `3e2212ed`:
21 model and 24 surface endpoints. The task records the seven model owners,
nine surface endpoint owners, unique-lookup consumer and lower semantic owners.
No owner-level specification decision was identified.

The audit found eleven direct maintained fixture callers and no removed-name
references in `CheckProof`, `CounterexampleActual`, SQL automation or simp
registrations. D4 and ADR 0025 conditions remain disjoint. Shared model/surface
registrations require coordination; the frozen expression work releases the
claims driver and shared context modules to this task.

The weaker no-error and optional-window formulas remain acceptance obligations.
The historical count/aggregate prototype does not establish their coverage.
The implementation below retains these contracts; combined Nix acceptance remains pending.

Assignment commit `d23ca1e9` passed independent Claude review with zero must and
zero should findings (`reviews/20261028T124145Z-d23ca1e9`). The earlier assignment
revision also passed without findings. The worker's source audit checked the
eleven fixture callers and absent automation references; the reviewer checked
the governing documents, paths and endpoint counts. Documentation source checks
passed; no implementation acceptance is implied.

## Implementation

Seven model output equations and eight surface equations replace all 45
projection endpoints. The eight resolver-only transports retain their exact
formulas and bodies. The shared source-output equation keeps support gating,
error precedence and optional windows; the SELECT-1 equation handles conditions
with arbitrary subquery runs under the existing fault-free premise. Generic
row/error projections and independent no-error guarantees remain available.

The count, scalar-column, EXISTS, NOT EXISTS and duplicate-key families use the
shared SELECT-1 fact. Aggregate output uses the general source equation; pragma
output uses the existing exact simple-query law. `QueryOutputFacts` owns the
moved context/source definitions; `SelectOneOutput` owns the SELECT-1 fact.
`FilteredDuplicateKeyEmpty` has no remaining declarations and is deleted.
The model adds those two module registrations; the surface removes the empty
owner's registration. No public provider roots change.

All eleven direct maintained fixture callers use the new semantic facts.
`ClaimsSum.sum_of_cents_output` proves an actual value-level result for every
matching table; its consumers derive integer 30, NULL on empty input, overflow,
row existence and nonemptiness. Unique lookup and pairwise/repeated grouping
consequences remain. Evaluator, admission, judge and conformance inputs do not
change. A source audit found no remaining removed endpoint names in packages,
implicit attributes, automation clients or checked references.

## Acceptance ownership and retirement

The temporary set is exactly the 16 files matching
`tests/surface/ClaimsQueryOutput*Migration.lean`, registered only by
`test_query_output_original_formulas` in `tests/surface_claims_test.py`.
Their 45 quantifier/premise/conclusion headers are copied from the assigned
baseline; declaration names are replaced by anonymous examples. They contain
no compatibility aliases. Remove the entire set and its registration only
after the coordinator records final combined Nix acceptance, then review the
retirement change. Do not retain a second matrix or a permanent inventory gate.

| Lasting boundary | Existing consumer or focused coverage |
| --- | --- |
| Arbitrary output/value predicate; aggregate empty input and overflow | `ClaimsSum` and `ClaimsAggregateLaws`; corrected `SuccessBalanceSuccess`. |
| Error before unsuccessful window binding; every tied LIMIT alternative | New applications of the complete source law in `ClaimsQueryCases`, using `QueryWindowExamples`. |
| Possible source fault; no-error without source cleanliness | `ClaimsQueryCases` applies the new source equation and retained independent no-error theorem to malformed `json_each`. |
| Function faults, unsupported subqueries and prepare errors | Existing `ClaimsMayFail`, `ClaimsScalarNoFrom` and per-family `ClaimsQueryCases`. |
| Certain count; scalar subquery exclusion and membership | Universal `ClaimsCount`/`ClaimsIn`; distinct first/row certainty instances in `ClaimsExpressionCongruence`. |
| EXISTS polarity, table metadata and case sensitivity | Universal `ClaimsExists`, `ClaimsTableInfo` and their concrete instances. Hidden cells remain explicit in the semantic equation. |
| Filtered grouping, NULLs, collation and partial-index invariant | `AccountSignupQueries`, `GlobalSignupInvariant`, `FilteredDuplicateKeyExamples` with its six native comparisons; retained grouping consequences. |
| Unique lookup and resolver-only transports | `ClaimsUniqueLookup`, `ClaimsDerived` and unchanged public transport signatures. |
| Trust | Existing claims audit adds the three generic output/result proofs; its original bridge and independent consumer audits remain. |

The original laws' independent premises stay in their current theorem
signatures; temporary formula recovery does not replace these ongoing
semantic consumers. S6 clients and automation remain owned by their existing
assertion-example and success suites.

## Validation record

Development diagnostics exercised `just dev-build`, the complete claims,
assertion-example and success test files, and focused reruns after caller
repairs. A source comparison checked all 45 original formula headers exactly.
These diagnostics are not acceptance evidence. The coordinator will run the
frozen integrated Nix checks, documentation build and verdict before retirement.

The local compiled report at `build/dev/d1-dependencies/dependencies.json`
selects 20 current owners. All 45 removed names are absent from its declarations,
external boundaries and type/body references. Five SELECT-1 family proofs
reference the shared SELECT-1 fact; aggregate references the source equation,
and pragma references the existing exact simple-row law.

The historical dependency report is older than `3e2212ed`. Its embedded source
matches that baseline byte-for-byte for 15 selected owners, including six model
families and their six surface counterparts. The comparison is limited to these
owners: the 18 old model endpoints use separate row/empty/error projection paths;
the six replacement facts use complete outputs. Duplicate-key source changed,
and the filtered owner is absent from the historical report. Their guarantees
come from the captured `3e2212ed` formulas and current compiled checks, with no
historical graph-reduction claim. The final matched Nix report remains pending.

Implementation `a6bfe314` passed independent Claude review with zero must and
one should finding (`reviews/20261028T134433Z-a6bfe314`). The finding identified
a stale current-consumer list in the resolver/foundation inventory. The follow-up
marks the removed owner and identifies the replacement filtered semantic law;
frozen inventory names and contracts remain unchanged.

Source-size accounting includes helpers, callers and fixtures; no speedup or
capability loss is claimed. The coordinator will record the final Nix source
count with temporary witnesses separated from maintained code.

Pending: follow-up documentation review, combined Nix
acceptance, temporary witness retirement, integration and push.
