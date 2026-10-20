# Status: the function catalog, text and type functions, and LIKE and GLOB (ADR 0015, slice 1)

Created 2026-10-20. Status: open.
Task file: [task](20261020-function-catalog.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D1, D2 and D3.

## Progress

- 2026-10-20: native facts checked with 3.51.0:
  - the library's `PRAGMA function_list` has 141 names (116 scalar, 27 aggregate or window);
    `narg` -1 is any number, and -N for N of 2 or more is at least N - 2;
  - the arguments resolve before the function: `nosuch(nocol)` is `no such column`;
  - `no such function: X` and `wrong number of arguments to function X()` keep the name as
    written;
  - `abs('-3')` is `3.0`, `abs('x')` is `0.0`, `iif(0,1,1,2,3)` is 2, `sign('x')` is NULL.

## Remaining

- All outcomes, tests, reviews, the slice verdict, the corpus, `just test-full`.
