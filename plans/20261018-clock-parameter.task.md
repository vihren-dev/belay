# The clock is an evaluation parameter (ADR 0013, step 6)

Created 2026-10-18. Status: open.
Status file: [status](20261018-clock-parameter.status.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), decision D6, "Order" step 6
(one HMS and printf port). Verdict: unchanged.

## Pull request

One pull request, stacked on the step 5 claim (#165). No change under `judge/` or
`integrity/`; `Contract.lean` and the approved files of `examples/atuin/approved/` do not
change. The verdict of every corpus is the same before and after.

## Outcome

1. **Clock parameter.** Expression evaluation, query runs, the joins, and the statement
   steps (`step`, `literalStep` and the write steps) take the statement's clock value.
   `runSqlAt` gives each statement the clock value of its position. No resolved statement
   is rewritten for a clock value.
2. **Time keywords.** `CURRENT_TIME`, `CURRENT_DATE` and `CURRENT_TIMESTAMP` evaluate to
   `DateFunction.value clock []` of `time`, `date` and `datetime`. `Resolved.Expr.date` has
   no `clock` field.
3. **Rows that read the clock.** A `VALUES` item or an omitted default that reads the
   clock stays an expression in the resolved INSERT row, and the step evaluates it at the
   statement's clock value and stores it with the column's affinity.
   `Statement.clocked`, `ClockCell`, `ClockRows.lean` and `ClockRowRules.lean` do not
   exist.
4. **Gone.** The `atClock` family, `scriptAtClock`, `StatementClockLaws.lean` and the
   hand-written `readsClock` family. Whether a statement reads the clock is one classifier
   over its expressions, with `Expr.any` (D7).
5. **One outcome for every clock.** For every script that reads no clock, every clock
   assignment gives the same outcome; the lemmas that `ContractProofs.lean`, the
   demonstrations and the examples use keep their meaning.
6. **One HMS and text port.** `ClockText.lean` keeps only what `Date/` does not have; the
   time keyword texts come from the date functions.

## Tests

- `just test-full`, `just test-nix` and `just test-scheduled` pass; the scheduled mutant
  suite kills every mutant, with anchors moved.
- The verdict of every corpus is unchanged, entry for entry, against step 5.
- `#guard` examples: each time keyword equals the date function without arguments at
  some clock values, including the default clock and a clock of zero; an INSERT with
  `DEFAULT CURRENT_TIMESTAMP` and a `VALUES` item with `datetime('now')` store the texts
  of their clock value, stored with the column's affinity; a script that reads no clock
  has the same outcome at two clock assignments.

## Key points

- **Soundness of the classifier.** `parseDateOrTime` reads the clock for `now`, `subsec`
  and `subsecond` after `bytesBeforeNul`; `namesClock` today does not cut at NUL. The
  classifier that decides "reads no clock" must cover every path to `DateTime.current`,
  or the one-outcome lemma states something false about SQLite.
- **The conformance harness** (`VerifierConformance/Case.lean`, `Predict.lean`) applies
  `scriptAtClock` today; it must run the script at the recorded clock instead, with the
  same refusal of a clock-reading script without recorded clocks.
- **Fault classifiers** (`Query.mayFail`, `mustFail`, `fails`, `JsonReady`) evaluate
  expressions; they need the clock value too.
- **Proof churn.** `SqlProofs`, `Laws`, `Preservation`, `LiteralPreservation`, `RowSpec`,
  `KeyMerge` and the examples state facts about `step`, `literalStep` and INSERT rows of
  values. The rows of a literal INSERT that reads no clock keep their stored values.
- **Mutants.** Anchors in the clock, INSERT and evaluator files move with the code.
