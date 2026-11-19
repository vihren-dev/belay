# Status of permutation invariance for unordered queries

Created 2026-11-19. Open. [Task](20261119-row-normal-form.task.md).

Shared/Execution/PossibleResults defines the comparators and the sort used
for unordered output. Queries/Evaluation/SelectWindowRules proves that the
sorted rows permute the input. Lean's List.Perm.eq_of_pairwise can compare
the sorted permutations once the order laws are available.
The implementation and acceptance checks are pending.
