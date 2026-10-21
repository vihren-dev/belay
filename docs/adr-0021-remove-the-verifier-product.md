# ADR 0021: Remove the migration verifier product

Date: 2026-10-21. Status: ACCEPTED on 2026-10-21 (owner instruction).
Implementation: [task](../plans/20261021-remove-verifier-product.task.md).
Audience: designers and reviewers.
Related: [ADR 0008](adr-0008-syntax-and-resolution-in-lean.md) (where resolution runs),
[ADR 0011](adr-0011-product-trust-and-development-integrity.md) (product trust and the judge),
[ADR 0016](adr-0016-model-and-surface.md) (the layer rules),
[ADR 0017](adr-0017-user-surface.md) (the user surface).

## Overview

The repository started as a migration verifier: a CLI (`migration-check`) that checks that a
SQLite migration keeps a database's business information, with a trusted kernel gate and an
installed runtime. Its first stable release is v0.1.1 (2026-09-28). The product is now the SQLite
model, which Lean developers use through the user surface (`Belay`). The verifier has no users,
and every change to the model, the parser or the harness must keep it working: its CLI, its gate,
its runtime build, its release job and about 45 test files.

This ADR removes the verifier product from the repository. The model, its conformance evidence,
the parser and the surface stay.

## Context

A survey of the source (2026-10-21) found these dependencies of the kept parts on the product:

- **The conformance runtime** (`build-support/default.nix`) is built on top of the installed
  runtime's Lean outputs, so the harness and the verdict job build the verifier library, the
  exporter and the gate's four programs. The conformance runner needs none of them; it imports only
  the model.
- **The restriction examples** (`conformance/restriction_examples.py`) run the gate's
  `migration-resolver` to show that each model restriction can be reached from SQL. They are the
  only conformance tool that calls a gate program.
- **The Lean test fixture** `lean_libraries` (`tests/runtime_fixtures.py`) requires
  `SqliteVerifier.olean`, although its model tests import only model and runner modules.
- **The documentation tools** (`tools/api_reference.py`, `tools/public_doc_inventory.py`) start
  from the `SqliteVerifier` library.
- **The model package** has codecs that exist only for the gate: `Codec/Source.lean` and
  `Codec/SourceExamples.lean` write Lean modules that import `SqliteVerifier`, and the script
  record (`ScriptRecord`, `decodeScriptRecord` in `Codec/Resolution.lean`) is the resolver's input.
- **CI**: the check job builds the installed runtime first, runs the bundle suite on macOS and
  packs the release archives; the `release` job and `adr3-p1.yml` serve only the product.

The judge does not depend on the product: its lock covers the judge, the claims, the corpora and
the native SQLite oracle, and every claim is about the model's agreement with SQLite.

## Decision

### D1. What is removed

- The CLI and its runtime: `migration_check/`, `bin/`, `packaging/`, `examples/`,
  `build-support/runtime.nix` and the Nix files only it uses (`lean4export.nix`,
  `case-seeds.nix`, `case_seed.py`, `library_lakefile.py`).
- The verifier library and the kernel gate: `packages/sqlite-verifier` and
  `packages/verifier-gate`, with the gate's codecs in the model (`Codec/Source.lean`,
  `Codec/SourceExamples.lean`, the script record) and their Python side
  (`belay/sqlite/syntax.py`'s `script_record`).
- The product's tests and suites: the `atuin`, `bundle`, `cli` and `kernel` suites, the host
  tests of the CLI, the runtime and the archive, and their fixtures.
- The product's CI: the `release` job, the archive steps of the check job, the bundle phase,
  `adr3-p1.yml`, and the justfile recipes `test-atuin`, `runtime-package` and the archive part of
  `package`.
- The product's documents: the install guide, the kernel gate and trust boundary documents, the
  CLI pipeline documents, the release notes and the pilot reports, and the engineering brief.
  The experiments that measure only the product (`experiments/adr-0003-latency`, `lake-cache`,
  `prepare-latency`) go too.

### D2. What stays, and how it no longer needs the product

- The model, the conformance runner, the harness, the judge, the corpora, the oracle, the parser
  and the surface stay.
- The conformance runtime is the toolchain, the model and the conformance runner, with the parser
  library. The judge's subject builds no product code.
- The restriction examples reach each restriction through the conformance runner, which already
  resolves a case with the model's `resolveSchemaAndScript`.
- The Lean test fixtures and the documentation tools start from the model's roots.
- The model keeps its laws, including the preservation laws (`PreservationLaws` and the
  others). They are facts about the model's semantics that a surface user can state and use; the
  verifier was only their first user.
- The tests that checked that the model builds without the verifier, or that the harness does not
  import the CLI, are deleted with what they guarded against.

### D3. Trust

With the gate gone, the repository has no product trust base (ADR 0011, decision 6). What a user
trusts is Lean's kernel over the model's definitions and the surface's terms (ADR 0017, D6), and
the conformance evidence that the judge grades. ADR 0011's development integrity (decisions 1 to
5: the judge lock, the verdict job, the protected files) stays. `.github/CODEOWNERS` loses the
product trust base's lines and keeps the integrity lines.

### D4. History

- The ADRs stay as the record of the decisions; each ADR that only the product used gets the
  line "Superseded by ADR 0021" in its header. ADRs that the kept parts still follow are amended
  where they name the product (ADR 0008's "Where resolution runs", ADR 0016 D2, ADR 0017 D6).
- The plans, the review records and the reports stay, as history. The frozen suite still reads
  some reports.
- The published releases (v0.1.x) stay on GitHub Releases as they are. No new release is made
  until the surface's first release (ADR 0016, "Deferred").

### D5. Order

The removal is one task, before the task that replaces the Python translation (ADR 0017, D2), so
that the translation task has no CLI or installed runtime to change. Its pull request changes
`.github/workflows/` and `.github/CODEOWNERS`, so it needs the owner's review. It changes no
claim, corpus, judge code or oracle, so the judge lock does not change.

## Consequences

- **Less to keep working.** A model or parser change no longer rebuilds or retests a CLI, a gate
  or an archive, and the verdict job builds less.
- **The predictions do not change.** The removal changes how the conformance runtime is built,
  not what it computes.
- **The repository's name stays** `sqlite-verifier` for now; renaming it is not part of this ADR.
- **The translation has fewer users.** When the Python translation is replaced (ADR 0017, D2),
  only the conformance harness and the surface use the translation; no installed runtime or CLI
  needs it.

## Alternatives considered

**Keep the product, frozen.** Rejected: frozen code still breaks when the model changes, so
every model change would keep paying for its tests and builds, with no user to serve.

**Move the product to its own repository.** Rejected for now: it would need its own copy of the
model, the parser and the harness, and nobody uses it. The git history keeps it, and a later
product can start from the surface.

## Not decided here

- A new verifier product built on the surface.
- The repository's name.
