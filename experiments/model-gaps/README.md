# The SQL that the user surface needs, in the out-of-scope corpus cases

Question: how many out-of-scope corpus cases each group of model work in ADR 0017's D5
brings into scope, and in which order the groups bring the most. This is the measurement
behind [ADR 0018](../../docs/adr-0018-surface-sql.md).

Measured on 2026-10-20 against the verdict of `main` after ADR 0015. Corpus v5 has 2,331
cases out of scope.

## How to reproduce

```sh
nix-build integrity/judge.nix -A verdict --no-out-link   # prints the verdict directory
python3 experiments/model-gaps/measure.py VERDICT/report.json conformance/corpus-v5 conformance/corpus-v4
```

## Method

- **Cases.** Only cases with the verdict `MODEL_UNSUPPORTED`.
- **Marks.** The lexical scan of the [functions measurement](../functions/README.md),
  with its list of modeled functions brought up to date after ADR 0015. A `PRAGMA
  foreign_keys` statement gets the mark `foreign-keys` instead of `pragma`.
- **Clean.** A case is clean for a set of groups when every mark of the case belongs to one
  of the groups. The counts are upper bounds: a restriction that a lexical scan does not
  see can keep a clean case out of scope.

## Result

See the table in ADR 0018. All groups together make 519 cases of v5 and 163 of v4 clean.
