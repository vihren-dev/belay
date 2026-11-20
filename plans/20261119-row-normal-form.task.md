# Permutation invariance of unordered query results

Created 2026-11-19. DONE. [Issue 446](https://github.com/vihren-dev/belay/issues/446).

Two lists of rows have the same normal form exactly when they are permutations
of one another, including repeated rows. The result applies to all model
values, including signed zero and NaN payloads. Value comparison in normal
order gives equality exactly for equal values. Row comparison gives equality
exactly for identical rows. Stable sorting equal permutations by any total,
transitive, antisymmetric Boolean order gives identical lists.

## Acceptance

Compile general Lean theorems for the value comparison, row comparison,
stable sort and normal form. Cover integer/real ties, distinct signed zeros,
NaN payloads, byte strings, prefixes and repeated rows. A surface proof for a
single table must show that splitting a read on a non-null condition and its
negation, and combining with UNION ALL, gives the same unordered output as
the original read. Use the permutation law and Lean's filter partition law.
Run the model and surface builds and the repository checks.

The existing sort and the representation of outputs are part of the contract.
The sort's permutation and sortedness theorems are in QueryLaws. SQL
comparison gives the first order. The normal comparator breaks ties between
storage representations that SQL compares as equal.
