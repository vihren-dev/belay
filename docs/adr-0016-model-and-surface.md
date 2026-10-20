# ADR 0016: Separate the model from the user surface

Date: 2026-10-20. Status: PROPOSED.
Implementation: after ADR 0015, SQL functions
([#194](https://github.com/vihren-dev/sqlite-verifier/pull/194)), is implemented; each
step gets its own task file.
Audience: designers and reviewers.
Related: [ADR 0006](adr-0006-model-boundary-and-execution-levels.md) (the model
boundary), [ADR 0010](adr-0010-lake-builds-and-artifact-cache.md) (one Lean package per
derivation), [ADR 0011](adr-0011-product-trust-and-development-integrity.md) (the judge
and its subject), [ADR 0013](adr-0013-model-structure.md) (model structure; it leaves
the split of `Resolution/` as a later mechanical change).

## Overview

The model will get a user surface: a library for Lean developers who state and prove
facts about SQLite databases, statements and programs. Its design is not part of this
ADR. Whatever that design is, the surface will have notation, elaborators, proof
automation and dependencies that the model must not have, and it will change more
often than the model.

Today the model has no boundary that a surface could stand on. Every declaration is
public, examples ship in the production library, and other packages import internal
modules by name. This ADR prepares the code base: it gives the model one public entry,
moves its examples out of the production library, renames it so that the name
`Belay.Sqlite` is free for the surface, creates an empty surface package with
dependency rules that a test enforces, and decides how CI and the trusted base treat
the two packages. It changes no semantics and no verdict.

## Context

Measured on `main` at f3c33b35 (2026-10-20):

| Fact | Value |
| --- | --- |
| Lean files in `packages/belay-sqlite` | 191 files, 18,265 lines |
| Declarations | 1,340 |
| Declarations marked `private` | 0 |
| Files that use Lean's module system | 0 of 226 in `packages/` |
| `Examples` files in the production libraries | 39 (38 in `Belay.Sqlite`, 1 in `Belay.Sqlite.Codec`) |
| Model definitions and theorems used by other packages, examples and kernel tests | about 129 of 1,121 (11%), counted by name |

Four facts follow from the code:

- **No public boundary.** All 1,340 declarations are public, and the documentation
  rules apply to all of them. The verifier library imports twelve model modules by
  name: the root, the codec, `SqlExecution` and nine `...Laws` modules. The conformance runner imports
  `Belay.Sqlite.QueryExamples` and `Belay.Sqlite.Resolution.SchemaScript`. The proofs of
  the engineering examples unfold `runSql`, `SqlState.finish` and
  `Resolved.Statement.readsClock`, so a refactor such as the steps of ADR 0013 breaks
  them.
- **Examples ship with the model.** The globs of the two libraries in
  `packages/belay-sqlite/lakefile.toml` include 39 `Examples` files. The verifier package
  already keeps its examples in a separate target, `EngineeringExamples`.
- **The model imports only `Init`.** `tests/test_model_ownership.py` enforces this. A
  surface needs at least `Std` (for example `Std.Do`, Lean's program logic), and it may
  need native code for SQL in Lean source and packages outside Lean. It cannot live in
  the model package.
- **The trusted base is the application library and the model library.** The kernel
  gate resolves trusted modules from the pinned sysroot and two installed roots
  (`requireLibraryRoots` in `packages/sqlite-verifier/GatePaths.lean`). The judge's
  subject is the conformance runtime, built from the model and the conformance
  package. Neither should grow when the surface grows.

The name `Belay.Sqlite` is the natural name of the library that users import. The model
uses it today, as its root module and as the namespace of every declaration. A surface
that defines its own types, for example a database type with more invariants than the
model's, needs the namespace without collisions.

## Decision

### D1. Three layers, each a Lake package

| Layer | Package | Root module | May import |
| --- | --- | --- | --- |
| Model | `packages/belay-sqlite-model` (`belaySqliteModel`) | `Belay.Sqlite.Model` | `Init` |
| Surface | `packages/belay-sqlite` (`belaySqlite`) | `Belay.Sqlite` | `Init`, `Std`, the model |
| Verifier | `packages/sqlite-verifier`, `packages/verifier-gate`, `packages/verifier-conformance` | as today | `Init`, `Lean` where they use it today, the model |

No package below the surface imports it. The verifier library, the gate and the
conformance runner stay on the model. The model's codec stays in the model package,
because the gate and the frontend use it.

### D2. The model has one public entry

The model package has two root modules that other packages may import:
`Belay.Sqlite.Model`, the model with its laws, and `Belay.Sqlite.Model.Codec`, the wire
format. Every other package imports only these roots. What the verifier library and the
conformance runner import by name today moves under these roots: the laws into
`Belay.Sqlite.Model`, and what the conformance runner takes from `QueryExamples` into a
definition file.

A test checks the imports of every Lean file outside the model package against the
table of D1 and this rule. It extends `tests/test_model_ownership.py`, which already
checks the model's own imports.

### D3. Examples leave the production library

The model's `Examples` files move to a separate Lean library, `ModelExamples`, as
`EngineeringExamples` does in the verifier package. CI builds it, and the model tests
use it. The installed runtime, the API reference and the documentation inventory leave
it out.

### D4. The model moves to `Belay.Sqlite.Model`

The directory `packages/belay-sqlite` becomes `packages/belay-sqlite-model`, every module
`Belay.Sqlite.X` becomes `Belay.Sqlite.Model.X`, and the namespace `Belay.Sqlite` of every
declaration becomes `Belay.Sqlite.Model`. Every caller changes in the same step: the Lean
packages, the engineering examples, the kernel tests, the Nix build, the conformance
tools and their mutant anchors, the tests and the documentation. As the repository's
rule for replaced code requires, no alias of an old name stays.

The step is mechanical. It is one change with no other work in it, as a Lean upgrade
is, and every corpus verdict must stay the same.

### D5. An empty surface package with its rules

The step after the move creates `packages/belay-sqlite` again, now as the surface
package: a `lakefile.toml` that requires the model, a root module `Belay.Sqlite` with a
module docstring that states the layer rules, its own Nix derivation, and its own suite
in `tests/nix_suites.json`, which at first holds the D2 check of its imports. The surface design, its contents and its later
dependencies come with their own ADR.

### D6. CI and the trusted base

- **CI.** The model's suites (`model`, `frozen`, `corpora`, `harness`, `sample` and the
  scheduled `mutants`) depend on the model package and not on the surface. A change to
  the surface runs the surface's suite and leaves the results of the model's suites to
  the Nix cache. `build-support/tests.nix` names the model's sources by package, not
  file by file, so that a moved file cannot leave a suite's inputs stale.
- **Trusted base.** The kernel gate keeps two installed roots, the application library
  and the model library. The installed runtime does not contain the surface package.
  Whether the verifier later accepts proofs that import the surface is a product
  decision for a later ADR. The judge's subject stays the conformance runtime, which
  does not contain the surface.

### D7. The module system: a measured decision

Lean's module system makes declarations private by default. Importing modules can
unfold a definition only when it is marked `@[expose]`, and Lake builds two more
artifacts for each module: a server olean and a private olean. It would let the model
hide its helpers and keep its executable definitions open to `decide` and to kernel
reduction.

It also touches the kernel gate, which reads oleans and replays their declarations, the
`lean4export` step, the Lake artifact cache of ADR 0010 and the conformance runner. This
ADR therefore decides only a prototype: convert a small slice of the model (for example
`ByteText`, `Identifier` and one `Laws` file) on a branch, and measure:

1. whether the gate, the proof exporter, the bundle checker and the conformance runner
   accept the new artifacts;
2. whether `decide` in the examples and the kernel checks of the conformance runner
   still work with the executable definitions exposed;
3. which declarations can be private, and how many docstrings the documentation
   inventory then no longer requires;
4. the change of build time, and of the modules that Lake rebuilds after a change to a
   proof.

The owner decides on adoption after the measurement. Without adoption, D2's test is the
boundary.

### Order and pull requests

Each step is a task file with its pull requests, and each keeps every corpus verdict:

1. **Examples target (D3).** Small, and independent of the rest.
2. **One public entry (D2).** The roots and the import test, before the move, so that
   the move changes import lines that are already few.
3. **The move (D4).** One mechanical change, after ADR 0015 and with no model slice in
   flight, so that no open branch has to replay it.
4. **The surface package (D5) and the CI changes (D6).**
5. **The module-system prototype (D7).** Its result goes into this ADR as an owner
   decision.

Steps 1 and 2 could start before ADR 0015 is done. The owner asked to start after it, so
the order above starts after it.

## Consequences

- **A refactor of the model cannot break callers through an internal name,** because
  other packages see only the roots. Changes to a root are visible in review as changes
  to the model's API.
- **The surface can change often without running the model's suites.** The `model`
  suite alone took 334 s when ADR 0013 measured it, so this is the main CI effect.
- **The trusted base stays as it is.** Notation, elaborators, automation and their
  dependencies stay outside the gate and the judge.
- **The move costs one large diff.** About 190 Lean files, the Nix build, the
  conformance tools and their mutant anchors, 27 test files and the documentation change
  together. Open branches conflict with it, which is why it waits until no slice is in
  flight.
- **Installed layouts change.** The runtime's model root has a new path and a new
  version, so Lake caches from before the move are not reused (`runtime_version`).
- **Engineering examples need new names.** Their `open Belay.Sqlite` becomes
  `open Belay.Sqlite.Model`, and their proofs keep the names of the model's root.

## Alternatives considered

**One package, with the module system as the only boundary.** Rejected: the surface
needs `Std` and may need native code, which the model's `Init`-only rule forbids, and
one package gives one Nix derivation, so a surface change would run the model's suites.

**The surface inside the verifier package.** Rejected: the verifier package is in the
trusted base and has its own product role. A library for Lean developers is neither.

**Keep the model's name and give the surface another one,** for example `Belay.Sql`.
This avoids the move of D4 and costs nothing now. It gives the model the short name that
users would import, and the surface the longer one. It is listed as an owner decision.

**Split `Resolution/` into directories at the same time.** Rejected for this ADR: ADR
0013 lists it as a later mechanical change, and two moves in one step make the diff
harder to review.

## Not decided here

- The design of the surface: its types, notation, elaborators and automation.
- Whether the installed verifier accepts proofs that import the surface.
- How the surface reads SQL in Lean source, which may need the parser library in the
  Lean process.
- Adoption of the module system (D7), until the prototype's measurement.

## Owner decisions

To be decided:

1. **The name of the model** (D4). Recommended: `Belay.Sqlite.Model`, which leaves
   `Belay.Sqlite` to the surface. The alternative keeps `Belay.Sqlite` for the model and
   gives the surface another name.
2. **The order** of "Order and pull requests", starting after ADR 0015.
3. **The module-system prototype** (D7): run it as step 5, or not at all.
