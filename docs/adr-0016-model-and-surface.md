# ADR 0016: Separate the model from the user surface

Date: 2026-10-20. Revised 2026-10-20, after ADR 0015 was merged and the rule for
supporting code (`AGENTS.md`, "Goal, core and supporting code") was adopted. Status:
PROPOSED.
Implementation: when the first code of the user surface is written.
Audience: designers and reviewers.
Related: [ADR 0006](adr-0006-model-boundary-and-execution-levels.md) (the model
boundary), [ADR 0010](adr-0010-lake-builds-and-artifact-cache.md) (one Lean package per
derivation), [ADR 0011](adr-0011-product-trust-and-development-integrity.md) (the judge
and its subject), [ADR 0013](adr-0013-model-structure.md) (model structure).

## Overview

The model will get a user surface: the library that Lean developers import to state
and prove facts about SQLite databases, statements and programs. The surface is core
work, because users meet the product through it. Its design is a separate decision;
the target user guide (in the product repository) describes it.

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
  surface needs `Std` (`Std.Do` for triples, in the guide) and native code (the parser,
  for `sql` and `db!` at elaboration). It cannot live in the model package.
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
requires the model package and may import `Init`, `Std` and the model. The package
starts with the code of its first prototype, not empty.

### D2. Layer rules, checked from the first day

- Nothing below the surface imports it: not the model, the verifier packages or the
  conformance runner.
- The surface imports the model only through the model's root module, `Belay.Sqlite`
  today (and the codec root, if it needs the wire format). An internal model module that the surface
  needs becomes part of the root in the same change.
- The installed runtime, the kernel gate and the judge's subject do not contain the
  surface.

The surface's suite holds a test of these rules. It is one check over the surface's
import lines, extended from `tests/test_model_ownership.py`.

### D3. The name

The guide gives the surface the name that users import, `Belay.Sqlite`, which the model
has today. Until the owner decides (owner decision 1), the surface package uses a
working name, `Belay.SqliteSurface` (package `belay-sqlite-surface`), so that no model
code moves for a name.

If the owner gives `Belay.Sqlite` to the surface, the model moves to
`Belay.Sqlite.Model` in one mechanical change of its own, before the surface has more
than its prototype: the fewer surface modules exist, the smaller the move. Every corpus
verdict stays the same, and no alias of an old name stays.

## Deferred, with their triggers

Each item is supporting work. It starts when its trigger happens, in its own task file,
and not before.

| Item | Trigger: the present problem that starts it |
| --- | --- |
| One public entry for the verifier and the conformance runner (two roots, laws under the root) | A model refactor breaks a caller through an internal module, or the verifier needs a model name outside the roots |
| Examples out of the production library (a `ModelExamples` target) | A measured cost: the installed runtime, the gate or the documentation inventory is slower or larger because of the examples |
| CI that skips the model's suites for a surface-only change | The surface has a suite whose changes rerun the model's suites, and the CI time of such changes is measured |
| Lean's module system (private declarations, `@[expose]`) | A surface user depends on a model helper that must stay internal, or the documentation inventory's cost of public helpers is measured |
| A separate repository for the surface (the guide's `vihren-dev/belay-sqlite`) | The first release of the surface |

## Order

1. The prototypes of the guide's open questions 8, 9 and 12, in the surface package of
   D1 with the rules of D2. They come with the surface's own ADR.
2. Owner decision 1, before the surface has more than its prototypes; if it gives
   `Belay.Sqlite` to the surface, the move of D3 follows at once, in its own change.

## Consequences

- **No preparation without a user of it.** The model, the verifier and CI stay as they
  are until surface code exists. The cost of this ADR is the D2 test and, if the owner
  chooses it, the move of D3.
- **The trusted base stays as it is.** Notation, elaborators, native code and their
  dependencies stay outside the gate and the judge.
- **The boundary starts small.** D2 checks only the surface's imports. The verifier
  keeps importing model modules by name until a trigger in the table needs more.
- **A late rename costs more.** If the owner decides the name after the surface grows,
  the move of D3 touches surface code too. Order item 2 keeps that cost small.

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

**The surface inside the verifier package.** Rejected: the verifier package is in the
trusted base and has its own product role. A library for Lean developers is neither.

## Not decided here

- The design of the surface: its types, notation, elaborators and automation (its own
  ADR, from the guide).
- How the surface runs the parser in the Lean process, and whether it needs the C
  library, a Lean port of the translation, or both (the prototypes of order item 1).
- Whether the installed verifier accepts proofs that import the surface.

## Owner decisions

To be decided:

1. **The name that users import.** Recommended: `Belay.Sqlite` for the surface, as the
   guide uses it, with the model moved to `Belay.Sqlite.Model` (D3). The alternative
   keeps `Belay.Sqlite` for the model and gives the surface another name, with no move.
2. **The order:** the surface's prototypes first, under the working name of D3.
