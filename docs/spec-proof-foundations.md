# Resolver certificates and ownership of proof primitives

Date: 2026-10-26. Revised: 2026-10-27 against `daa15385`. Status: PROPOSED.
Audience: implementers and reviewers.
Decision: [ADR 0026 D3, D6 and D7](adr-0026-semantic-proof-boundaries.md).
Evidence: [resolver and import findings](../experiments/proof-boundaries/resolver-import-findings.md)
and [row-engine findings](../experiments/proof-boundaries/row-engine-findings.md).
Targets: [resolver declarations, ownership, imports and deferred work](spec-proof-resolver-foundation-targets.md).
The compiled prototypes used `3fe5caef`; this revision is source-reviewed and
does not claim that those prototypes compile against the new production source.

## Required resolver behavior

For each successful `resolveStatement`, one certificate provides:

- The next state is `state.after resolved`, with no validity or mode premise.
- For any limits under which the input catalog is valid, the resolved statement
  has its schema link to that catalog. No saved-state or execution-mode premise
  is needed for this field.
- In execution mode, full input-state validity at the context's profile limits
  implies full next-state validity at those limits.

One complete statement-syntax dispatch proves these facts together. Reusable
catalog and write transports assemble existing leaf resolver facts. They
preserve write preparation failures, rule wrapping and statement kind. Bundling
must not make every field require the strongest field's assumptions.

The dispatch covers the current `renameTable`, `renameColumn` and `insertSelect`
syntax cases as well as the older cases. Reuse `RenameOutcome` and its
`applyCatalog`/`valid` facts, and `resolveInsertQuery_form`/`resolveInsertQuery_same`.
Resolved `rewrite` and `insertSelect` retain their catalog actions; their
`SchemaLink` cases impose no condition. The three CREATE/ADD catalog-action
facts now belong to `Resolution/ApplyCatalogSpec`, not `ResolveStateSpec`.

`resolveStatement` is now the result projection of `resolveStatementTraced`,
whose run carries the resolver's name trace. Use the existing `statement_arms`
equations when needed. Preserve the result/trace projection and existing source
registrations; this task introduces neither a parallel resolver nor a new trace
certificate. The semantic certificate remains about successful result states.

Replace the three top-level proofs `resolveStatement_after`,
`resolveStatement_schemaLink` and `resolveStatement_valid`. Migrate consumers to
the certificate and delete replaced names rather than retaining aliases.
The original formulas remain acceptance obligations. Keep independent leaf
resolver facts that carry actual semantics or serve other callers.

`resolveStatement_applyCatalog_valid`'s mathematical claim remains derivable
for all resolved statements, including controls. Ordinary statements use the
next catalog; controls leave `applyCatalog` unchanged. Current and saved
catalogs still follow their distinct transaction semantics. Resolution-only
mode must not be granted execution-mode validity guarantees.

The script consumer is now `runScriptAllFrom_admittedWith`: its guarantee covers
every complete execution, including alternatives from INSERT SELECT. Preserve
that quantifier. Step consumers retain the actual output/next connection and
the separate `others : List StatementExecution`; their existing premises decide
when alternatives are absent. A resolver certificate alone gives no singleton
execution guarantee.

## Required foundational ownership

Shared definitions and facts can be imported by their instances without a
cycle or unrelated instance imports. This applies to resolver state validity,
state transition and schema linkage, and to leaf transport facts. The
prototype's imports of files containing old top-level proofs are temporary
ownership constraints; the production certificate must sit below its consumers.

Relocate the following four existing facts to appropriate foundational modules
and migrate their consumers. Their formulas remain unchanged:

| Fact | Current feature owner |
| --- | --- |
| `Collation.compare_eq_of_binary` | `ForeignKeySelfLookup` |
| `generatedCells_plain` | `NormalizedFieldRows` |
| `Database.tableAt_of_table` | `AddColumnFromValid` |
| `Database.table_of_findTable` | `TableSourceLaws` |

The foundational proof layer must not import those feature owners merely to
obtain these facts. The historical experiment proved all four without the old owners.
It does not establish one optimal common module for them; use the existing
domain owners rather than a miscellaneous utility collection.

The bodies of surface `Values`, `Script` and `ValueDisplay` are unchanged from
the historical narrow-import probes. Revalidate their imports on current source;
the old compilation does not establish sufficiency after dependency changes. Narrow those
imports to their actual providers while retaining their exports, instances,
syntax, simplification behavior and checked documentation. Keep public umbrella
entry points available. Whole-package splitting and an automatic import
rewriter are outside scope.

Query and agreement specs also require definition moves. Each move has one
owner and migrated consumers; parallel work must not copy shared definitions
into separate modules. ADR 0025 has additional preservation ownership changes
that remain governed by its own specification.

The new surface `ReadCertificate`, `ReadAnalysis`, `ReadCertificatePreservation`
and `CertifiedQueryCommutation` serve simple-table read and migration claims.
They do not replace the resolver-state certificate. Retain their separate
resolution, width, calmness, frame and branch-shape obligations; more general
expression congruence alone does not remove their no-fallible-call, clock or
counter restrictions. Compile these downstream consumers after ownership moves.

## Row-engine decision

Keep the specialized ordinary and FK trigger preservation proofs. Neither the
broad `RowKeeps` prototype nor the narrow program/list prototype justifies an
implementation task. Do not add the experimental contracts to the public API.

A later proposal must show a concrete simplification including caller witnesses.
It must preserve separate success/stop predicates, FK permitted-work conditions,
FAIL versus rollback behavior, and invariants at physical phase boundaries.
There is no requirement that an invariant hold after every micro-operation.

## Acceptance checks

- Kernel-check the three replaced resolver formulas and the full applied-catalog
  validity formula with their original assumptions as migration witnesses.
  The universal certificate proof covers every syntax constructor; no extra
  fixture per constructor is required. Retain distinct control, rename, INSERT
  SELECT, traced-result, write-rule and saved-catalog semantics through existing
  coverage or focused missing cases.
- Verify by proof/source dependency inspection that the new dispatch does not
  invoke the replaced top-level proofs, directly or through helper closures.
  Compile all resolver and statement-preservation consumers, including the new
  failed-step, plain-write and read-only frame proofs. Preserve complete-run
  quantification and existing actual/alternative-step distinctions.
- Recompile the four relocated primitive formulas and their consumers. Confirm
  their foundational owners do not depend on the former feature owners.
- Compile the full affected surface bodies and downstream public clients with
  the narrowed imports. Inspect exports, attributes and notation; stored proof
  references alone cannot establish source-level import sufficiency.
- Record project import closures with the same scope as the experiment.
  Historical probes at `3fe5caef` measured 580 to 75, 142 and 148 modules.
  Measure the actual current before/after baseline; those counts neither describe
  `daa15385` nor become permanent thresholds. Build timing is a separate claim.
- Run existing documentation, proof, Nix and conformance checks at their required
  cadence; all new checks have timeouts and the standard axiom policy.
- Report production source changes including certificates, transports, caller
  migrations and formula tests. The experiment demonstrates three statement
  dispatches becoming one, not a measured whole-codebase reduction.

No execution behavior, judge input, corpus or SQL feature scope changes. The
standalone experiment checker is sufficient historical evidence and does not
become a new production CI suite.

## Test lifetime

Apply ADR 0026's retirement rule. Resolver projection witnesses, duplicate
primitive proofs, baseline/narrow module copies, old-endpoint dependency
inspections and import/source measurements are temporary acceptance work.
Normal compilation of relocated declarations and migrated consumers replaces
duplicate probes. No frozen import count or old-name inventory becomes a CI gate.

Keep concise coverage of independently conditional certificate fields, including
unconditional state equality, arbitrary schema-link limits and execution-mode
state validity. Preserve control/saved-catalog meaning and the existing axiom
policy. Retain any unique contract coverage until a migrated client or focused
regression supplies it; then delete redundant active witnesses and registrations
after final Nix acceptance. Record retirement in the existing status file.
Row-engine prototypes remain historical experiments, with no production tests
or obligation to port them to the new API.

## Assignment and coordination

Resolver certification and the four primitive/import changes can be assigned
separately. Definition placement is a dependency of each shared proof, not a
reason to create a global foundation package first. Create implementation task
and status files shortly before assignment, batching edits for that decision.
