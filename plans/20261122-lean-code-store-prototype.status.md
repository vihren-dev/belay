# Status: a prototype of the Lean code store extractor

Date: 2026-11-22. Status: OPEN.
Task: [20261122-lean-code-store-prototype.task.md](20261122-lean-code-store-prototype.task.md).
Specification: [the Lean code store](../docs/records/spec-lean-code-store.md),
[ADR 0032](../docs/adr/adr-0032-lean-code-store.md).

## Source files

- `experiments/lean-code-store/extractor/`: the Lean fact reader (`lean-code-store-facts`), one
  process for each module, in the environment of the module and its imports.
- `experiments/lean-code-store/lean_code_store/`: keys (`keys.py`), folding rules (`folding.py`),
  user of a mention (`mentions.py`), rows (`rows.py`), local row files (`store.py`), the run
  (`run.py`, `inputs.py`), the `clickhouse-local` load and query (`clickhouse.py`).
- `experiments/lean-code-store/fixture/`: the fixture package and `expected-rows.json`.

## Tests

`python3 -m pytest -c experiments/lean-code-store/pytest.ini experiments/lean-code-store/tests`:
unit tests of keys, folding, text cuts and mention users, and the fixture test (needs Lean and
Lake; builds the fixture copy, compares rows, checks the second run and an edit). The
experiment has its own `pytest.ini`, so the repository's upload of test observations is not
loaded.

## Progress

- 2026-11-22: task file written. No code.
- 2026-11-22: first prototype. It implements the rules of "Generated constants" as the
  specification writes them, for the constants of the selected modules. For a target outside
  the selection it applies only rules 1 and 5: rules 2 and 3 need the ranges of all constants
  of the target's file, which the prototype does not read for Lean's library. Input: the Nix
  packages of `just theorem-dependencies` for this revision. Local measurement, not evidence:
  1,617 modules in 196 s; a second run extracts 0 files in 4 s; with the rules as written, no
  rule decides 13,108 constants. The report of this commit does not name a generated constant
  whose parents end in a reported constant; the next commit names them (161 in a run of the
  same rules). The next commits record this and correct the rules.
- 2026-11-22: review fixes: a generated constant whose parents end in a reported constant is
  reported with that cause; tests for a changed build product, an indented `deriving instance`
  command, a generated target in Lean's library (`Nat.casesOn`), and the `clickhouse-local`
  load and query.
- 2026-11-22: review fixes: the text of a `deriving instance` command ends at the last type of
  its `for` list; extractor version 2, so the store extracts again the file versions of
  version 1; the fixture uses `Prod.mk` and `Prod.fst` as the only source of `Prod`; the query
  test has a target with two users.
