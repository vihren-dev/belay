# Task: a prototype of the Lean code store extractor

Date: 2026-11-22. Status: OPEN.
Decision: [ADR 0032](../docs/adr/adr-0032-lean-code-store.md) (PROPOSED).
Specification: [the Lean code store](../docs/records/spec-lean-code-store.md).
Status file: [20261122-lean-code-store-prototype.status.md](20261122-lean-code-store-prototype.status.md).

## Problem

The owner asked for a prototype (2026-11-22). The specification gives rules that no program
ran: the rules for generated constants, the user of a mention, the key of a file version.
Four review rounds each found declarations of the tree that break a rule. A prototype that
runs on the real tree shows which rules hold, and gives the first exact list of declarations
with one user.

## What must be true when the task is done

- A prototype under `experiments/lean-code-store/` reads a matched build of the default
  selection (the library trees of the packages, as the dependency report selects them) and
  writes the rows of the six tables of the specification as local files.
- The prototype loads the rows into `clickhouse-local` with the DDL of the specification and
  runs the single-use query of the specification. It does not write to a ClickHouse server:
  the database is an open owner decision.
- A second run on the same tree extracts no file version. A run after an edit of one file
  extracts only the file versions whose key changed. The record gives the counts.
- A findings record `docs/records/lean-code-store-prototype-findings.md` (audience: designers
  and reviewers; it says that the results are local and that no check accepted them) gives:
  - for each rule of "Generated constants": the count of constants that it decided, and
    examples;
  - the constants that no rule decided and the helpers with no parent or more than one, by
    cause;
  - for mentions: how many got their user from the container, from the range, and none;
  - the count of rows of each table and the time of the extraction;
  - the count of single-use candidates by kind, with 20 examples that a person read against
    the source, and the false candidates among them with their cause;
  - each statement of the specification that the run showed wrong, with the declaration
    that shows it.
- The specification and the ADR are corrected where the run showed them wrong, in commits of
  their own.

## Tests

- Unit tests of the pure parts (key computation, folding rules, user of a mention) on small
  fixtures, each with a timeout, in less than 10 seconds together.
- One fixture Lean package under the experiment with a case for each rule: a structure, an
  inline `deriving` clause, a `deriving instance` command for two classes and two types, a
  `where` function, a private declaration, an `example`, a docstring reference, a
  declaration named `Foo._helper`, two modules that declare the same name. A test builds it
  and compares the rows with an expected file. It can be marked as needing Lean.

## Points to know

- `tools/theorem_dependency_exporter.lean` and `tools/theorem_dependencies.py` are the
  starting point. The exporter loads all modules into one environment; the specification
  needs each module in the environment of its own imports.
- `.ilean` files: keys `decls`, `references`, `directImports`. Their `decls` are not
  complete.
- The earlier inventory tools are in other workspaces and are not on `main`:
  `/home/codex/work/sqlite-verifier-ownership-embedding/experiments/ownership_full/`
  (`SourceParser.lean`, `FullInventory.lean`, `CommandOrigins.lean`). Read them; do not
  change those workspaces.
- The store is supporting code. Keep the prototype small. It is an experiment: it does not
  become a `just` target or a CI job in this task.
- Tension: the folding rules read facts about imported constants, so a module-by-module
  load costs time. Measure it.
- Local results are not evidence. The record says so.
