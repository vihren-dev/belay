# ADR 0016: Separate the model from the user surface

Date: 2026-10-20. Revised 2026-10-20, after ADR 0015 was merged and the rule for
supporting code (`AGENTS.md`, "Goal, core and supporting code") was adopted; the owner
decided the names the same day (D3). Status: PROPOSED.
Implementation: when the surface ADR's first prototype starts (see "Order").
Audience: designers and reviewers.
Related: [ADR 0006](adr-0006-model-boundary-and-execution-levels.md) (the model
boundary), [ADR 0010](adr-0010-lake-builds-and-artifact-cache.md) (one Lean package per
derivation), [ADR 0011](adr-0011-product-trust-and-development-integrity.md) (the judge
and its subject), [ADR 0013](adr-0013-model-structure.md) (model structure).

## Overview

The model will get a user surface: the library that Lean developers import to state
and prove facts about SQLite databases, statements and programs. The surface is core
work, because users meet the product through it. Its design is a separate decision;
the target user guide (in the product repository) describes it. The product will later
model PostgreSQL and MariaDB too, with the same surface for users, so the names leave
room for more engines than SQLite (D3).

The surface needs a home that the model cannot be: it imports `Std` and will call the
SQLite parser as native code, and the model imports only `Init`. This ADR decides that
home and the rules that keep the model and the trusted base free of the surface. It
plans no other preparation. The structural changes that the first proposal of this ADR
made in advance (one public entry, examples out of the production library, a rename of
the model, an empty surface package, a module-system prototype) each wait until a
present problem needs them; the section "Deferred, with their triggers" lists them.

## Context

Measured on `main` at fd9c2ad3 (2026-10-20), after ADR 0015:

| Fact | Value |
| --- | --- |
| Lean files in `packages/belay-sqlite` | 222 files, 21,944 lines |
| `Examples` files in the model package | 45 |
| Declarations marked `private` | 0 |
| Files that use Lean's module system | 0 |
| Lean code that calls native code (`@[extern]`, `--load-dynlib`) | none |
| Model modules that other packages import by name | 16, mostly `...Laws` modules |

Facts that bear on the decision:

- **The model imports only `Init`.** `tests/test_model_ownership.py` enforces this. The
  surface needs `Std` (`Std.Do` for triples, in the guide), `Lean` (for its
  elaborators) and native code (the parser, for `sql` and `db!` at elaboration). It cannot live in the model package.
- **The trusted base is the application library and the model library.** The kernel
  gate resolves trusted modules from the pinned sysroot and two installed roots
  (`requireLibraryRoots` in `packages/sqlite-verifier/GatePaths.lean`). The judge's
  subject is the conformance runtime. Neither should grow when the surface grows.
- **The surface's first risks are technical, not structural.** The guide's open
  questions name them: the parser inside the Lean process and the editor's Lean
  server (question 8; nobody has tried it), the translation from the parser's syntax
  to the model's syntax in Lean instead of Python (question 9), and a `Std.Do`
  instance for programs over every environment and row order (question 12). Each
  needs a prototype, and each can change what the surface package needs.
- **No caller suffers from the model's structure today.** No surface code exists, so
  the missing public boundary, the examples in the production library and the shared
  name `Belay.Sqlite` cost nothing yet. Their costs appear only once the surface has
  code, users or a release.

## Decision

### D1. The surface is its own Lake package

The first surface code goes into a new Lake package with its own Nix derivation and its
own suite in `tests/nix_suites.json`, created by the change that adds that code. It
requires the model package and may import `Init`, `Std`, `Lean` (its elaborators use
Lean's elaboration API) and the model. The package
starts with the code of its first prototype, not empty.

### D2. Layer rules, checked from the first day

- Nothing below the surface imports it: not the model, the verifier packages or the
  conformance runner.
- The surface imports the model only through the model's root module, `Belay.Sqlite`
  today (and the codec root, if it needs the wire format). An internal model module that the surface
  needs becomes part of the root in the same change.
- The installed runtime, the kernel gate and the judge's subject do not contain the
  surface.

The surface's suite holds a test of these rules, extended from
`tests/test_model_ownership.py`: it reads the import lines of every Lean file in the
repository, for the first two rules, and the packages that the installed runtime, the
gate and the conformance runtime are built from (`build-support/`), for the third.

### D3. The names

Users import `Belay`. Everything specific to one engine lives under that engine's name,
`Belay.Sqlite` for SQLite, and later `Belay.Postgres` and `Belay.MariaDB` (owner
decision 1):

| Part | Package | Root module and namespace |
| --- | --- | --- |
| The surface | `belay` in `packages/belay` | `Belay`, with the SQLite surface under `Belay.Sqlite` |
| The SQLite model | `belaySqliteModel` in `packages/belay-sqlite-model` | `Belay.Sqlite.Model` |

With one engine, every part of the surface is specific to SQLite, so all surface code
lives under `Belay.Sqlite`. The module `Belay` imports it and defines nothing of its
own. A part that is the same for every engine moves into `Belay` only when a second
engine exists (see "Deferred, with their triggers").

The move is one mechanical change of its own, with no other work in it, and it comes
before the first surface code, so that no surface module has to move. Every caller
changes in the same change: the Lean packages, the engineering examples, the kernel
tests, the Nix build, the conformance tools and their mutant anchors, the tests and the
documentation. Every corpus verdict stays the same, and no alias of an old name stays.

## Deferred, with their triggers

Each item is supporting work. It starts when its trigger happens, in its own task file,
and not before.

| Item | Trigger: the present problem that starts it |
| --- | --- |
| One public entry for the verifier and the conformance runner (two roots, laws under the root) | A model refactor breaks a caller through an internal module, or the verifier needs a model name outside the roots |
| Examples out of the production library (a `ModelExamples` target) | A measured cost: the installed runtime, the gate or the documentation inventory is slower or larger because of the examples |
| CI that skips the model's suites for a surface-only change | The surface has a suite whose changes rerun the model's suites, and the CI time of such changes is measured |
| Lean's module system (private declarations, `@[expose]`) | A surface user depends on a model helper that must stay internal, or the documentation inventory's cost of public helpers is measured |
| An engine interface in `Belay`: the parts of the surface that are the same for every engine (scripts, programs, queries as propositions, triples, equivalence), with each engine as an instance | The model of a second engine (PostgreSQL or MariaDB) exists, so that the shared parts come from two real engines |
| A separate repository for the surface (the guide's `vihren-dev/belay-sqlite`) | The first release of the surface |

## Order

This ADR plans no work of its own. It takes effect when the surface's own ADR starts
its first prototype (the guide's open questions 8, 9 and 12 are the candidates):

1. The move of D3, in its own change, because the surface's first code needs the name.
2. The change of the first prototype creates the surface package of D1, with the test
   of D2.

Amended 2026-10-21: a script makes the move of D3, so the move can be prepared as a local
commit while other model work is still in review, on top of it. Its pull request opens only
when no model pull request below it is open, and the script then runs again on that base,
so that no open branch has to merge the move.

## Consequences

- **No preparation without a user of it.** The model, the verifier and CI stay as they
  are until surface code is about to exist. The cost of this ADR is the move of D3 and
  the D2 test.
- **The trusted base stays as it is.** Notation, elaborators, native code and their
  dependencies stay outside the gate and the judge.
- **The boundary starts small.** D2 keeps the surface out of the layers below it and
  makes the surface use the model's root only. The verifier keeps importing model
  modules by name until a trigger in the table needs more.
- **The move costs one large diff.** About 220 Lean files, the Nix build, the
  conformance tools and their mutant anchors, the tests and the documentation change
  together. Open branches conflict with it, so its pull request waits for a time with no
  model work in flight (see the amendment in "Order"). The runtime's model root gets a new path, so Lake caches from before the move
  are not reused.

## Alternatives considered

**Prepare the code base first (the first proposal of this ADR, 2026-10-20).** It gave
the model one public entry, moved the examples, renamed the model, created an empty
surface package with CI changes, and prototyped Lean's module system, all before the
surface had code. Rejected after the rule for supporting code: each step answered an
anticipated surface, none answered a present problem, and together they cost a move of
about 220 files and changes to CI and the gate before the surface's real risks (the
parser in Lean, the translation, the program logic) were known. The table of deferred
items keeps each step with the problem that would start it.

**One package, with the module system as the only boundary.** Rejected: the surface
needs `Std` and native code, which the model's `Init`-only rule forbids, and one package
gives one Nix derivation, so a surface change would rebuild and retest the model.

**Keep `Belay.Sqlite` for the model, and give the surface another name.** It avoids the
move of D3. Rejected by owner decision 1: users import the surface, so the surface gets
the short name.

**`Belay.Sqlite` as the name that users import** (the first form of owner decision 1).
Replaced the same day: with PostgreSQL and MariaDB to come, the import must not name
one engine, so users import `Belay` and the engine's name marks only what is specific
to it.

**An engine interface now, with SQLite as its only instance.** Rejected under the rule
for supporting code: a shared framework for one case. Its shape would come from one
engine and be wrong where the second one differs, for example in typed parameters,
error states or transactions. The deferred table keeps it with its trigger.

**The surface inside the verifier package.** Rejected: the verifier package is in the
trusted base and has its own product role. A library for Lean developers is neither.

## Not decided here

- The design of the surface: its types, notation, elaborators and automation (its own
  ADR, from the guide).
- How the surface runs the parser in the Lean process, and whether it needs the C
  library, a Lean port of the translation, or both (the surface ADR's prototypes).
- Whether the installed verifier accepts proofs that import the surface.
- How the engine appears in the user's code with one import, for example in the type of
  a database (`Sqlite.Database`), so that `db!` and `run` follow from the type (the
  surface ADR).

## Owner decisions

Decided on 2026-10-20:

1. **The names.** Users import `Belay`; the parts specific to SQLite live under
   `Belay.Sqlite`, and the SQLite model moves to `Belay.Sqlite.Model` (D3). PostgreSQL and
   MariaDB will get their own names under `Belay`, with the same surface.
