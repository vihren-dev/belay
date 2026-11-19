# Status of permutation invariance for unordered queries

Created 2026-11-19. Open. [Task](20261119-row-normal-form.task.md).

Shared/Execution/PossibleResults defines the comparators and normalForm.
Shared/Execution/QueryEval defines stableSort. Queries/Evaluation/SelectWindowRules proves that the
sorted rows permute the input. Lean's List.Perm.eq_of_pairwise can compare
the sorted permutations once the order laws are available.
NormalFormLaws proves that value and row comparison distinguish exact model
values, that a stable sort with a total transitive antisymmetric order gives
the same result on permutations, and that row normal forms are equal exactly
on permutations. SelectCompoundCases checks a one-table UNION ALL split,
repeated rows and ties between model values. Its proof uses the filter
partition and permutation laws. The focused test is
tests/surface_select_sources_test.py. The slice checks are pending.

Review clarified the checked names in the four public law statements and
the SQL partition and tie cases covered by the test.

The second review found no issues. The full test and verdict checks are pending.
