# Status: the results that SQLite may give (ADR 0018, slice 6)

Created 2026-10-21. Status: open.
Task file: [task](20261021-possible-results.task.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D6.

## Progress

- 2026-10-21: the task file, from ADR 0018 D6, ADR 0017 D3 and the guide's "Row order", and from
  the recorder's tie groups.
- 2026-10-21: outcomes 1 to 5. `PossibleResults.lean` (normal form, tie groups, choices,
  `Query.possibleResults`, `Query.possibleOn`), laws in `PossibleResultsLaws.lean`
  (`Query.slices_results`, `Query.normalResult_mem`, `Query.possibleResults_length`,
  `Query.possibleResults_ne_nil`), kernel examples in `PossibleResultsExamples.lean`, and the
  runner's check (`VerifierConformance/PossibleOutputs.lean`, `Pass.lean`, `Case.lean`). The
  replay of every agreeing case of the frozen corpora with the check: 4048 of 4048 still agree.
  The authored corpus (`conformance/authored_possible_results.py`, 8 cases, writer
  `possible_result_evidence.py` for corpus 47) agrees with kernel proofs, and the four mutants
  (`possible_result_mutants.py`) are each killed.

## Remaining

- The local verdict and `just test-full`.
