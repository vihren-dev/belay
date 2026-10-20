# Status: the exact numeric functions (ADR 0015, slice 2)

Created 2026-10-20. Status: open.
Task file: [task](20261020-numeric-functions.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D4.

## Progress

- 2026-10-20: native facts checked with 3.51.0: `floor(3)` is an integer, `floor('3.7')` is
  3.0 and `floor('x')` NULL; `trunc(-0.5)` and `ceil(-0.5)` are `-0.0` (written `0.0`);
  `round(2.5)` 3.0, `round(-2.5)` -3.0, `round(1.005, 2)` 1.0, `round(-0.001, 2)` `-0.0`;
  `sqrt(-1)` and `mod(1, 0)` are NULL; `mod(7, 3)` is 1.0 and `mod(-7, 3)` -1.0.

## Remaining

- All outcomes and tests.
