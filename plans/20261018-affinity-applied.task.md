# Affinity is applied, not refused (ADR 0013, step 4)

Created 2026-10-18. Status: DONE (pull request #162 and its claim).
Status file: [status](20261018-affinity-applied.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), decision D4, "Order" step 4,
owner decision 2 (restricted cases become predictions; measured over every corpus first).

## Pull requests

- **Pull request A (subject):** the model, the docs of the restriction registry and the
  tests. No change under `judge/` or `integrity/`; `Contract.lean` does not change.
- **Pull request B (judge, owner approval):** adds every frozen case that agrees after
  pull request A and was restricted before to `mustAgree` in `judge/claims.json`, with
  the new `integrity/judge.lock.json`. It lists the cases.

## Outcome

1. **Comparison affinity.** `Resolved.Expr.compare` carries the affinity of the
   comparison, which resolution computes as SQLite's `sqlite3CompareAffinity` does: when
   both operands have an affinity, NUMERIC if either is INTEGER, REAL or NUMERIC, else
   BLOB; else the affinity of the one operand that has one; else none. A column has the
   affinity of its declared type (BLOB without one), `CAST` the affinity of its type,
   and every other expression, `+x` included, none. Evaluation applies it as SQLite's
   comparison opcodes do: with INTEGER, REAL or NUMERIC, a TEXT operand that looks like a
   number becomes that number and every other value stays; with TEXT, a numeric operand
   becomes its text when the other operand is TEXT; with BLOB or none, nothing changes.
2. **Values as conditions.** A condition of any value is true as SQLite's
   `sqlite3VdbeBooleanValue` gives it: an integer that is not zero, or a TEXT or BLOB
   whose numeric prefix (`Value.toReal`) is not zero. `x IS [NOT] TRUE|FALSE` is the truth
   test of any operand.
3. **Restrictions removed.** `textToNumber`, `numberToText`, `mixedAffinityComparison`
   and `valueAsCondition` leave the registry, with `Operand`'s refusals (`conversion`,
   `affinityIssue`, `mayBeText`), `isCondition` and `isTruthValue`. The resolver keeps
   the affinity of each operand while it resolves, and stores only the comparison's.
4. **Three registries.** Each restriction kind belongs to one registry, given by a
   classifier: *unsupported* (scope not yet modeled), *undecided* (SQLite behaviour that
   depends on implementation order) and *unrepresented* (the IR loses a fact the
   evaluator needs). The ids do not change; the docs table groups the kinds by registry,
   and every *unrepresented* kind's docstring gives the reason.

## Tests

- Before the model commit: the classifier over every frozen corpus with the change; no
  case is `DISAGREE` or `HARNESS_ERROR`, and the cases restricted by the four kinds before
  are listed with their new verdicts.
- `just test-full`, `just test-nix` and `just test-scheduled` pass; the verdict
  (`nix-build integrity/judge.nix -A verdict`) differs from step 3 only in cases that
  were `MODEL_UNSUPPORTED` and are now `AGREE`.
- `#guard` examples: an INTEGER column against `'1'`, an untyped column against `1`, two
  literals, `CAST(x AS TEXT) = 1`, `+x`, a REAL column against a large integer, and
  conditions `'1ab'`, `'abc'`, `0.9`, `x'31'`.
- The restriction registry tests (`tests/restriction_registry_test.py`) check the
  classifier and the grouped docs table.

## Key points

- **REAL affinity.** Do not apply `storeValue .real` to an INTEGER operand: it would make
  `realColumn = 9007199254740993` equal through a double. SQLite converts only TEXT
  operands for a numeric affinity.
- **TEXT affinity.** SQLite stringifies a number only when the other operand is TEXT;
  say in the docstring that the order would be the same otherwise.
- **Every filter changes at once.** `truthy` decides WHERE, ON, UPDATE, DELETE and UPSERT
  filters and AND, OR and NOT.
- **No `noAffinity` node.** ADR 0013 proposes one for `+x`, because it expected the
  affinity to be read from the resolved expression. The resolver knows each operand's
  affinity while it resolves, and the comparison stores the result, so `+x` needs no
  node. Record this in the ADR's implementation notes.
- **D7 wording.** D7 names `mayBeText` and `isCondition` among functions that stay where
  D4 keeps them; D4 removes both.
- **`transitive1-81x`.** These cases test SQLite's transitive WHERE terms; check natively
  that the plain semantics give the same rows.
- **Mutants and guards.** `query_mutants.null_equals_null` anchors `Comparison.apply`, and
  `no_such_column` builds an `Operand`. `MergedNameExamples.lean` and
  `UsingExamples.lean` guard the removed restrictions. `tests/cli_refusal_test.py` uses
  `text-to-number` as its example restriction.
