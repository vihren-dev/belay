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

- 2026-10-20: the work is based on both the ADR branch (#194) and the slice 7 stack of ADR
  0014 (#191, #192), so that corpus 36 follows corpus 35.
- 2026-10-20: the catalog, the scalar form and the slice's functions (commit "function catalog,
  text and type functions, LIKE and GLOB").
  - Lean `Resolution/FunctionCatalog.lean` (141 built-in names and `match`),
    `Resolution/ScalarFunction.lean`, `Resolution/FunctionCalls.lean` (`callOperand`,
    `scalarCall`, `starCallIssue`), `Functions/Scalar.lean`, `Functions/Utf8.lean`,
    `Functions/Pattern.lean` (`patternCompare` with fuel), `Functions/Text.lean`,
    `Functions/Quote.lean`, `Functions/Examples.lean`; `Resolved.Expr.scalar`; the prepare
    errors `noSuchFunction` and `likelihoodArgument`.
  - `Resolved.Expr.isFallibleCall` replaces the JSON-only test where a fault matters (query
    and write readiness, `NoWrites`, constant VALUES, CHECK, index keys, generated
    columns); `Expr.fault_of_plain` now has a fallible-call premise.
  - Frontend: `LIKE`, `GLOB`, `REGEXP` and `MATCH` operators as calls; `like(`, `glob(`, `if(` and
    `replace(` as calls.
  - Tests run for this commit: `function_catalog_test` (the Lean catalog against `PRAGMA
    function_list`), `test_model_package` (158 modules), `mutant_guards`, `restriction_registry`,
    `resolution_cleanup`, the frontend tests, the kernel proofs of every authored corpus,
    `conformance_authored_test`, the restriction examples, the corpus writer of corpus 36, the
    query and number mutants (the coalesce mutant now changes `callOperand`), and the three
    new mutants of `conformance/function_mutants.py`. `conformance/authored_text_functions.py`
    has 38 cases, all agree.
  - `sqlite_version()` and `sqlite_source_id()` stay unmodeled (task amended).

- 2026-10-20: review of the slice commit: seven must findings (catch-all match arms in
  `ScalarFunction.apply` and the pattern searches, `Text.lean` over 200 lines, a missing proof
  sketch, the replaced `functionCall` and `scalarFunctionName`, JSON-only restriction
  messages, and the literal length limit). Fixed in "refactor: review of the function
  catalog" with `Functions/Codes.lean` (159 modules). Tests: the fast tests, the kernel proofs
  of corpus 36, the function mutants and the restriction examples.

- 2026-10-20: slice end. Corpus 36 recorded (38 cases). Local verdict with corpus 36 claimed:
  383 cases of corpus v5 and 11 of v4 newly agree (v5: 1,365 → 1,748), corpus 36 has 38
  AGREE, and no case leaves AGREE or disagrees. The first `just test-full` failed in the
  documentation inventory: undocumented constructors of `TrimSide` and `PatternResult`, and
  `let rec` helpers that the inventory cannot classify. Fixed in "fix: documented helpers of
  the text functions" (`classMembers`, `instrSearch`, `replaceAll`, `trimFront`, `trimBack`,
  `unhexBytes`, `unistrBytes`).

## Remaining

- `just test-full` after the fix; the claims of corpus 36 and the 394 upstream cases go into
  the PR B of the ADR.
