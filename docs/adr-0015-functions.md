# ADR 0015: SQL functions

Date: 2026-10-20. Status: ACCEPTED on 2026-10-20 (owner instruction to implement it, after the decisions of #194).
Audience: designers and reviewers.
Evidence: [the functions measurement](../experiments/functions/README.md).
Related: [ADR 0012](adr-0012-query-semantics.md) (query semantics, JSON and date
functions), [ADR 0013](adr-0013-model-structure.md) (one resolved form per rule, the
restriction registry), [ADR 0014](adr-0014-schema-features.md) (the slice process),
[ADR 0011](adr-0011-product-trust-and-development-integrity.md) (claims and the judge).

## Overview

The model has few SQL functions: COUNT, MIN, MAX, SUM and AVG of one argument, COALESCE,
seven JSON functions, and the six date and time functions. Every other call is the model
restriction `unmodeled-function`, also a name that is no function at all. Functions are
the largest single reason that corpus cases stay out of scope. This ADR adds SQLite's
deterministic built-in functions in six slices that the measurement orders: core text and
type functions with the `LIKE` and `GLOB` operators, exact numeric functions, JSON functions that build or edit text, JSONB,
three aggregates, and `printf`. It also adds SQLite's prepare errors of calls: `no such
function` and the argument count of each function. Window functions, the transcendental
math functions and the functions that read the connection stay out of scope (see "Not
decided here").

## Context

The measurement reads the out-of-scope cases of corpus v5: 3,011 of its 4,376 cases.

- **Scale.**
  - The model refuses 784 cases for a function reason.
  - A lexical scan finds a function that the model does not have in 955 cases.
  - 745 of those use no other feature that the scan sees ("clean"). For them, the
    functions are the only missing piece that the scan can see.
- **Order.** The clean cases when the model supports each group in turn:
  - core text and type functions: 375. `typeof` (157 clean), `substr` (140) and `quote`
    (56) are the largest.
  - exact numeric functions: 394 in total;
  - `printf` and `format`: 395;
  - JSON functions that build or edit text: 515;
  - JSONB: 685;
  - `group_concat`, `string_agg` and `total`: 692.
- **Upper bounds.** The clean counts are upper bounds. A restriction that a lexical scan
  does not see, such as an unmodeled argument form, can still stop a case. Each slice
  measures its real effect with the verdict, as in ADR 0014.
- **Where the rest are.** The other cases that call an unmodeled function also use another
  feature. Most often it is a subquery, a compound select, `||`, `CASE` or `BETWEEN`, which
  a later ADR on expressions covers.

The model already has what the functions need:

- text values are byte lists, which the kernel reduces;
- `RealText.lean` ports SQLite's `printf` conversion `%!.15g`;
- `NumberText.lean` and `NumberConvert.lean` port SQLite's text-to-number conversions;
- `Json/` reads, renders and queries JSON text;
- `Fault` gives a call that can fail at run time its failure (`ExprEval.lean`).

**The kernel and REAL values.** The verdict proofs use `decide +kernel` with no native
axioms. Lean 4.34's kernel reduces the IEEE operations `+`, `-`, `*`, `/`, `sqrt`,
`abs`, the conversions between integers and floats, and `toBits`. It does not reduce
`floor`, `ceil`, `round`, `log`, `exp` or the trigonometric functions (checked on
2026-10-20). Each function that this ADR adds is written with operations that the kernel
reduces.

## Decision

### D1. One function catalog, with SQLite's prepare errors

- **The catalog.** A new module lists each built-in function of the pinned SQLite build
  that a call can name: its name and the numbers of arguments it accepts. These are the
  built-in functions of `PRAGMA function_list` in the pinned library: 141 names, 116
  scalar and 27 aggregate or window (`min` and `max` are both). The `sqlite3` shell adds a
  few more, such as `regexp`, which the library does not have. The list is written in Lean. A test compares it with `PRAGMA function_list` of the native build, with native
  SQLite as the oracle.
- **Errors.** Resolution reports SQLite's prepare errors from the catalog:
  - `no such function: X` for a name that is no function;
  - `wrong number of arguments to function X()` for a number of arguments that the
    function does not accept.

  Both are prepare errors, so a case with a misspelled function agrees with SQLite
  instead of being out of scope.
- **Restriction.** A function of the catalog that the model does not describe is
  `unmodeled-function`, as today. Its message names the function.
- **Checks at prepare time.** Some functions have further prepare errors, for example
  `likelihood` with a second argument that is not a constant between 0.0 and 1.0. Each
  slice adds the checks of its functions and checks each one natively.

### D2. One resolved form for scalar calls

- **The form.** A new `Resolved.Expr.scalar (function : ScalarFunction) (arguments)`
  takes every new scalar function. `ScalarFunction` is an enumeration with one
  constructor for each function, so a missing case is a compile error and the mutation
  tests can name each rule.
- **Existing forms stay.** The JSON and date forms (`Resolved.Expr.json` and
  `Resolved.Expr.date`) stay as they are, and the new JSON functions join
  `JsonFunction`. Moving them into `ScalarFunction` would change many proofs for no
  gain in behaviour.
- **Evaluation.** Each family has its own evaluation module (text, numbers, JSON
  editing, JSONB). `Expr.evaluate` dispatches to it. A function that can fail at run
  time gives its `Fault`, as JSON functions do today: for example `abs` of the
  smallest integer is SQLite's `integer overflow`.
- **Collations and affinity.** Scalar `min` and `max` compare their arguments under the
  collation of the left-most argument that has one, as SQLite does. The other functions
  have no affinity of their own, as in SQLite.

### D3. Text and type functions (slice 1)

- **Functions.** `typeof`, `length`, `octet_length`, `lower`, `upper`, `substr` and
  `substring`, `instr`, `replace`, `trim`, `ltrim`, `rtrim`, `hex`, `unhex`, `quote`,
  `char`, `unicode`, `unistr`, `unistr_quote`, `concat`, `concat_ws`, `ifnull`, `nullif`,
  `iif` and `if`, `likely`, `unlikely`, `likelihood`, scalar `min` and `max`, `abs`,
  `sign`, `zeroblob`, `like`, `glob`, `sqlite_version` and `sqlite_source_id`.
- **Text rules.**
  - Text is UTF-8 bytes. `length`, `substr`, `instr` and `unicode` count characters as
    SQLite does, by UTF-8 lead bytes, also in text that is not valid UTF-8. A BLOB is
    counted in bytes.
  - `lower` and `upper` change only the ASCII letters, as in a build without ICU.
  - A number given as text is converted by SQLite's rules: integers in decimal, and
    REAL values with `%!.15g` (`RealText.lean`).
- **`quote`.** It writes a REAL with `%!.15g` when that text converts back to the same
  value, and otherwise with more digits, as SQLite does (`quote(1.0/3)` is
  `3.333333333333333148e-01`). The exact rule is checked natively in the slice.
- **`LIKE` and `GLOB`.** This slice also adds the operators `LIKE`, `NOT LIKE`, `GLOB` and
  `NOT GLOB`, with `ESCAPE`, and the functions `like` and `glob`. The functions take the
  pattern first: `like(pattern, text [, escape])` (owner decision 3). Checked natively:
  - `LIKE` ignores the case of ASCII letters only (`'Àb' LIKE 'àb'` is 0), and it ignores
    the collation of its operands.
  - `GLOB` is case sensitive, and `[^...]` negates a character class; `[!...]` does not.
  - `_` matches one UTF-8 character, and a number is compared as its text.
  - An `ESCAPE` of more than one character fails while the statement runs: `ESCAPE
    expression must be a single character`.
  - `PRAGMA case_sensitive_like` stays out of scope, as every PRAGMA; `REGEXP` has no
    built-in function in the library.

### D4. Exact numeric functions (slice 2)

- **Functions.** `round`, `floor`, `ceil` and `ceiling`, `trunc`, `sqrt`, `pi`, `degrees`,
  `radians` and `mod`.
- **Exact.** Each of them is an exact IEEE operation, or a rounding to an integer, so its
  value does not depend on the C library. The kernel reduces `sqrt` and the division and
  multiplication of `degrees` and `radians`. `floor`, `ceil` and `trunc` use the integer
  conversion for values below 2^52 and keep larger values. `round` follows SQLite's
  `roundFunc`: an integer conversion for small values, else the `%!.*f` printf
  conversion and a conversion back.
- **Not here.** The transcendental functions are `ln`, `log`, `log2`, `log10`, `exp`,
  `pow` and `power`, and the trigonometric and hyperbolic functions. Their results come
  from the platform's C library, and the kernel cannot compute them. They stay the
  restriction `unmodeled-function` (see "Not decided here").

### D5. JSON functions that build or edit text (slice 3)

- **Functions.** `json_set`, `json_insert`, `json_replace`, `json_remove`, `json_patch`,
  `json_array`, `json_object`, `json_quote`, `json_error_position` and `json_pretty`.
- **Aggregates.** `json_group_array` and `json_group_object`.
- **How.** They build on the JSON reader, paths and renderer of `Json/`. Edits follow
  SQLite's rules for paths that do not exist, for array indexes past the end (`$[#]`) and
  for RFC 7396 merge patches. The output is SQLite's minified JSON text. The
  `json_pretty` output uses SQLite's indentation.
- **Arguments that are JSON.** An argument that came from another JSON function is JSON,
  not text, so `json_array(json('[1]'))` nests the array. The model tracks this "JSON
  subtype" of a value in evaluation, as SQLite does, and only within one expression.

### D6. JSONB (slice 4)

- **Functions.** `jsonb` and the `jsonb_*` forms of the functions in D5 and of
  `json_extract`.
- **Format.** They return a BLOB in SQLite's documented binary JSON format, byte for
  byte. Each function that reads JSON also reads a JSONB BLOB. Today a BLOB argument of
  a JSON function is a `may` fault (`Fault.ofJson`); with this slice it is read as JSONB.
- **Encoding.** SQLite's encoder has choices, such as the size of each header and when
  text needs escapes. The model makes the same choices, and the authored corpus covers
  each one.

### D7. Aggregates (slice 5)

- **Functions.** `group_concat` and `string_agg` with an optional separator, and `total`.
- **Order.** `group_concat` joins the values in the order in which the group sees its
  rows, the same order in which `MIN` and `MAX` see them today.
- **`total`** is the REAL sum that never overflows, by SQLite's summation (`Summation.lean`).

### D8. `printf` and `format` (slice 6)

- **The conversions.** A port of SQLite's `sqlite3_str_vappendf` over byte lists. It
  generalizes the `%!.15g` port of `RealText.lean` to all conversions (`d`, `i`, `u`, `f`,
  `e`, `E`, `g`, `G`, `x`, `X`, `o`, `c`, `s`, `z`, `q`, `Q`, `w`, `%`), flags, width and
  precision, including `*`.
- **Order.** The measurement gives this slice almost no clean cases: `printf` appears
  next to other features. It is last for that reason. Application SQL uses it, so it stays
  in this ADR.

### Order and pull requests

The slices follow the measured order, and each has its own task file:

1. the function catalog and its prepare errors, the text and type functions, and the `LIKE`
   and `GLOB` operators (D1, D3);
2. the exact numeric functions (D4);
3. the JSON functions that build or edit text (D5);
4. JSONB (D6);
5. the aggregates (D7);
6. `printf` and `format` (D8).

Each slice works as in ADR 0014:

- an authored corpus that covers its functions, with each prepare error and run-time
  failure;
- mutants for its main rules;
- the verdict of every corpus;
- a pull request B that claims the cases that newly agree.

### Implementation notes

- Slice 1 (2026-10-20), details checked natively that D1 to D3 do not state:
  - The library registers one function apart from the built-in ones, `match` with two
    arguments, which fails when it runs; the catalog keeps it, so `MATCH` stays
    `unmodeled-function` instead of `no such function`.
  - SQLite resolves the arguments of a call before the function, also for an aggregate:
    `WHERE sum(nocol)` is `no such column`.
  - `like(` and `glob(` parse as the `LIKE_KW` token, and `if(` and `replace(` as keywords; the
    frontend maps them as calls.
  - A function result has no affinity and no collation, also `likely(x)` and `ifnull(x, y)`.
  - `sqlite_version()` and `sqlite_source_id()` stay `unmodeled-function`: expression
    resolution has no profile to give the release.
  - A function that can fail while the statement runs is, like a JSON function, a model
    restriction in a CHECK constraint, an index key and a generated column, and fails as
    SQLite does only in a query without `FROM` (`Resolved.Expr.isFallibleCall`).

## Consequences

- **Fewer out-of-scope cases, more prepare errors.** A misspelled or unknown function
  becomes SQLite's `no such function` error instead of a restriction. A call with the
  wrong number of arguments becomes SQLite's error for every function.
- **The catalog follows the build.** The function list is a fact of the pinned SQLite
  build. A new SQLite version in a profile can change it, and the test against
  `PRAGMA function_list` shows the change.
- **Evaluation grows.** `Expr.evaluate` dispatches to four new families. The
  evaluation of a function stays a pure function of its arguments, so the existing laws
  about evaluation do not change.
- **Kernel cost.** Text functions over long strings and JSONB encoding cost kernel time
  in the verdict proofs. Each slice measures the CI time of the model suite, as in ADR
  0014.
- **The measured gain is an upper bound,** about 690 cases of corpus v5. Most of the
  other function cases need an expression form first (`||`, `CASE`, `BETWEEN`,
  subqueries).

## Alternatives considered

- **Keep refusing unknown names as a restriction.** Rejected: SQLite refuses them when
  it prepares the statement, so the model can report the same error, and the cases then
  agree.
- **Move the JSON and date forms into one `call` form now.** Rejected: it changes proofs
  and corpora for no change in behaviour. A later refactor can do it.
- **Compute the transcendental functions with Lean's `Float`.** Rejected: the kernel
  cannot reduce them, so no verdict would have a kernel proof, and their results depend on
  the C library of the platform.
- **Native evaluation of functions through the parser library.** Rejected: the model
  must describe the semantics in Lean, so that proofs can use them (ADR 0006).

## Not decided here

- **Window functions** (`OVER`, `FILTER`, `rank` and the others) and **`ORDER BY` in an
  aggregate call.** They need a window stage in queries, and they get their own ADR.
- **`DISTINCT` in an aggregate call.** It appears in 57 out-of-scope cases, and none of
  them is clean. It can join a slice when the measurement shows a gain.
- **The transcendental math functions.** A software implementation that gives
  glibc's results bit for bit is possible but large. It needs its own decision.
- **Functions that read the connection or are not deterministic:** `random`,
  `randomblob`, `changes`, `total_changes`, `last_insert_rowid`, `sqlite_offset`,
  `sqlite_compileoption_*`, `load_extension` and `sqlite_log`. They stay
  `unmodeled-function`.
- **The expression forms** that most other function cases need (`||`, `CASE`, `BETWEEN`,
  `IN`, subqueries). They get their own ADR. `LIKE` and `GLOB` are in slice 1 (D3).

## Owner decisions

Decided on 2026-10-20:

1. **JSONB stays in this ADR** (D6, slice 4). It brings about 170 clean cases.
2. **`printf` and `format` stay in this ADR** (D8, slice 6), because application SQL uses
   them, although the corpus gives them almost no clean cases.
3. **The `LIKE` and `GLOB` operators join slice 1** (D3), with the functions `like` and
   `glob`. They add one clean case of corpus v5 (376 instead of 375), since the other cases
   with `LIKE` or `GLOB` also use another feature; application SQL uses them.
