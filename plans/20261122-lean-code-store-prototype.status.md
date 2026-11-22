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
  specification writes them. Input: the Nix packages of `just theorem-dependencies` for this
  revision (built here, 7 min 43 s). Local run on 1,617 modules: 196 s; a second run extracts 0
  files in 4 s. With the rules as written, 13,108 constants are reported by no rule; the next
  commits record this and correct the rules. Unit and fixture tests pass.
