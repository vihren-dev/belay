# Resolver certificates and import ownership

Date: 2026-10-26. Audience: designers and reviewers.

## Decisions

Adopt one resolver certificate dispatch for the three existing successful-result
claims. Preserve the separate assumptions of its fields. The experiment shows
that the three traversals can share their statement cases without calling the
old dispatch theorems. This is a consolidation of proof control flow; the leaf
resolver facts remain useful independently.

Adopt the demonstrated narrow imports for the three surface modules and relocate
the four demonstrated primitive facts to suitable lower owners. The experiments
establish that these moves are feasible. They do not establish minimum import
sets, a production rebuild result, or an elapsed-time improvement.

## Resolver formulas

`ResolverCertificate.lean` contains a proposition about the resolved statement
and complete next resolver state. `resolve_certificate` in
`ResolverDispatch.lean` proves it from successful `resolveStatement` resolution.
Its fields retain these distinct requirements:

| Field | Additional premise | Conclusion |
| --- | --- | --- |
| `after` | None | `next = state.after resolved` |
| `link` | `state.catalog.Valid limits`, for any `limits` | `resolved.SchemaLink state.catalog` |
| `valid` | Execution mode and `state.Valid context.profile.limits` | `next.Valid context.profile.limits` |

`ResolveState.Valid` means the current catalog is valid and any saved transaction
catalog is valid. The schema-link field needs neither saved-catalog validity nor
execution mode. Its limits need not equal the context profile's limits. The state
equation requires neither kind of validity. The certificate itself therefore
takes only the success equation; each conditional field carries its own premise.

`ResolverApplications.lean` recovers the complete formulas of
`resolveStatement_after`, `resolveStatement_schemaLink`, and
`resolveStatement_valid`. Its fourth witness, `applied_original`, also recovers
the full formula of `resolveStatement_applyCatalog_valid`. That witness covers
control statements through `applyCatalog_of_control`, without adding a
non-control premise. The witnesses are experiment checks, not proposed
compatibility aliases.

The BEGIN case retains an existing saved catalog or saves the current one.
COMMIT discards the saved catalog. ROLLBACK restores a saved catalog when present.
The validity field preserves the corresponding current/saved facts in each case.
Setting pragmas retain their exact state equation. The write transport handles
both prepare-error results with unchanged state and statements wrapped with
write rules. These cases must remain in the implementation acceptance checks.

## Shared reasoning and source inventory

`ResolverDispatch.resolve_certificate` performs one case split over the syntax
statement. It assembles `CatalogCertificate` fields from leaf facts and transports
them through catalog attachment or write attachment. It does not project from
any old top-level successful-resolution theorem.

As an additional read-only check, the existing dependency report's body-reference
closures were followed from the 47 explicitly named production resolver roots
used by `ResolverCertificate.lean` and `ResolverDispatch.lean`. None reaches
`resolveStatement_after`, `resolveStatement_schemaLink`,
`resolveStatement_valid` or `resolveStatement_applyCatalog_valid`. This checks
those named roots against the frozen production report; it is not a newly
exported dependency graph for the prototypes.

The old declaration spans are in
`packages/belay-sqlite-model/Belay/Sqlite/Model/`:

| Source scope | Physical lines | Nonblank, noncomment lines |
| --- | ---: | ---: |
| `Resolution/ResolveStateSpec.lean:96–189`, state equation | 94 | 94 |
| `ResolveStatementFacts.lean:20–63`, schema link | 44 | 44 |
| `ResolveStatementValid.lean:31–115`, state validity | 85 | 85 |
| Original declaration spans | 223 | 223 |
| `ResolverCertificate.lean`, whole file | 80 | 52 |
| `ResolverDispatch.lean`, whole file | 128 | 118 |
| New shared core | 208 | 170 |
| `ResolverApplications.lean`, experiment witnesses | 56 | 39 |

The old spans exclude docstrings; including each declaration's docstring gives
249 physical lines. The new whole-file counts include comments, imports,
namespaces and axiom-print commands. This inventory supports the smaller shared
dispatch, but it is not a complete production migration delta. It omits changes
to consumers and module ownership. No elaboration or rebuild speedup is inferred.

The experiment imports the existing endpoint-owning modules to obtain definitions
and leaf facts. Production must resolve those mixed responsibilities without an
import cycle. In particular, `ResolveStatementValid.lean` currently owns both
`ResolveState.Valid` and `resolve_valid`, the latter using the old validity
dispatch. A new certificate module cannot import that file while the file also
imports the certificate for its script proof. Put shared prerequisites below the
dispatch and its consumers, or reorganize the existing owner to achieve the same
acyclic dependency. Keep the existing independent leaf guarantees available.

## Primitive ownership

`ImportsPrimitives.lean` re-proves four existing formulas with their existing
proof bodies and more general module ownership:

| Primitive | Existing owner |
| --- | --- |
| BINARY equality implies equality under every built-in collation | `ForeignKeySelfLookup.lean:12` |
| Generated-cell evaluation is identity when all columns are plain | `NormalizedFieldRows.lean:40` |
| Database table lookup supplies the corresponding catalog shape | `AddColumnFromValid.lean:67` |
| A named catalog table supplies the database table and stored rows | `TableSourceLaws.lean:17` |

The prototype imports `Comparison`, `AdmittedCellLaws`, `DatabaseFacts` and
`Resolution.CatalogSpec`. Its combined project import closure has 191 modules
and contains none of the four existing owning modules. The facts therefore do
not require their current specialized owners. This combined-file check does not
identify the unique or smallest import set for each fact.

Production relocation should keep the mathematical statements and update their
actual consumers. Choose an owner below those consumers and check the resulting
module graph for cycles. Keep source-level exports, attributes and instances
when they are part of a moved API. The experiment does not authorize retaining
duplicate facts or compatibility aliases.

## Surface imports

`imports.py` makes disposable baseline and narrowed copies of `Values`, `Script`
and `ValueDisplay` from the selected production packages. It changes only the
model umbrella import. Both copies compile; their declarations, proof bodies,
Verso documentation, instances, exports and display registration are unchanged.
In particular, `Values` retains its source-level exported model names, which
compiled body-reference edges alone would not fully describe.

| Surface module | Baseline project import closure | Narrow project import closure |
| --- | ---: | ---: |
| `Values` | 580 | 75 |
| `Script` | 580 | 142 |
| `ValueDisplay` | 580 | 148 |

The closure counts include reachable selected-project modules, not Lean or Std
modules. The parser covers all actual import-line forms in the selected source;
no reachable `Belay.*` import in these closures is missing from that source map.
The output records the module lists and exact compiled copies. These are source
import-reachability measurements, not declarations required by each proof.

A successful narrowed copy does not establish that every downstream module
builds after the production edit. A downstream module may depend on names that
the former umbrella import made available transitively. The implementation must
rebuild the affected consumers and add their own needed imports where appropriate.
No timing claim follows from the closure-size reductions alone.

## Validation limits

The standalone Nix experiment target supplies the compiler diagnostics and audited
proof closures. It rejects warnings and axioms outside `propext`,
`Classical.choice` and `Quot.sound`. The resolver transport laws, dispatch, four
formula witnesses and four primitive facts request explicit axiom checks.

This experiment changes no production resolver or imported module. Script-level
resolver proofs and all downstream callers have not been migrated. Final
implementation acceptance must verify the original formulas, remove replaced
dispatches, rebuild affected consumers and check the resulting import ownership.
