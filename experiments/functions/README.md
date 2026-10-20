# SQL functions in the out-of-scope corpus cases

Question: which SQL functions keep corpus cases out of the model's scope, and which groups
of functions would bring the most cases into scope when the model supports them? This is
the measurement behind [ADR 0015](../../docs/adr-0015-functions.md).

Measured on 2026-10-20 against the verdict of the ADR 0014 stack tip (#192). Corpus v5 is
the newest and largest upstream corpus: 4,376 cases from SQLite 3.51.0's own test suite,
of which 1,365 agree and 3,011 are out of scope. No case disagrees. This README reports
corpus v5.

## How to reproduce

```sh
nix-build integrity/judge.nix -A verdict --no-out-link   # prints the verdict directory
python3 experiments/functions/measure.py VERDICT/report.json conformance/corpus-v5
```

`measure.py` takes several corpus directories and prints JSON for each one.

## Method

- **Cases.** Only cases with the verdict `MODEL_UNSUPPORTED`.
- **Scan.** The scan is lexical and reuses the tokenizer of the
  [schema features measurement](../schema-features/README.md): strings, blobs, quoted names
  and comments do not count. It reads the migration, and the CREATE statements of the
  setup, whose index keys, CHECK constraints and generated columns the model resolves.
- **Calls.** A call is a name followed by `(` after an operator, `(`, `,` or a keyword that
  can come before an expression. A name after another word is a type name such as
  `VARCHAR(10)`, and a name after `INTO`, `TABLE`, `ON` or `REFERENCES` has a column list.
  PRAGMA arguments do not count. `min` and `max` with two or more arguments are the scalar
  functions, counted as `MIN2` and `MAX2`.
- **Modeled today.** COUNT, MIN, MAX, SUM and AVG of one argument, COALESCE, `json`,
  `json_extract`, `json_type`, `json_valid`, `json_array_length`, the six date and time
  functions, and `json_each` in FROM.
- **Other features.** The marks of the schema features measurement (triggers, views,
  `PRAGMA`, `WITH`, subqueries, compound selects, window functions and others), and the
  expression and query forms that the model refuses today: `BETWEEN`, `CASE`, `||`,
  `IN (...)`, `LIKE` and `GLOB`, `IS` other than `IS NULL`, bitwise operators and `%`,
  bound parameters, `DISTINCT` and `HAVING`, `EXPLAIN`, a call with `DISTINCT`, `FILTER` or
  `OVER`, and a table-valued function other than `json_each`.
- **Clean.** A case is clean when it calls at least one function that the model does not
  have and has no other feature. A clean case is the best estimate of a case that support
  for its functions brings into scope. A restriction that the scan does not see can still
  stop it, so the clean counts are upper bounds.

**Check of the scan.** The model refuses 784 cases for a function reason (an unmodeled
function, `DISTINCT` in a call, or `ORDER BY`, `FILTER` or `OVER` in a call). The scan finds
an unmodeled function in 955 cases, and 745 of them are clean.

## Results (corpus v5)

The functions with the most uses (*uses*: out-of-scope cases that call it; *refused*:
cases that the model refuses for a function reason; *clean*: cases with no other feature):

| Function | Uses | Refused | Clean |
|---|---|---|---|
| `typeof` | 172 | 156 | 157 |
| `substr` | 156 | 141 | 140 |
| `jsonb` | 143 | 110 | 117 |
| `quote` | 58 | 55 | 56 |
| `json_set` | 35 | 31 | 31 |
| `round` | 33 | 30 | 30 |
| `json_remove` | 33 | 32 | 32 |
| `printf` | 32 | 16 | 18 |
| `json_patch` | 32 | 32 | 31 |
| `char` | 30 | 10 | 10 |
| `json_insert` | 28 | 23 | 13 |
| `json_array` | 25 | 24 | 24 |
| `json_object` | 23 | 23 | 20 |
| `jsonb_array` | 20 | 19 | 19 |
| `group_concat` | 19 | 7 | 6 |
| `json_replace` | 19 | 19 | 19 |
| `jsonb_set` | 17 | 16 | 16 |
| `likelihood` | 16 | 12 | 12 |
| `min` with two or more arguments | 16 | 13 | 10 |
| `format` | 15 | 5 | 5 |
| `max` with two or more arguments | 14 | 13 | 11 |

The other functions have 15 uses or fewer each. Among them are the other `jsonb_*`
functions, `json_error_position`, `json_quote`, `likely` and `unlikely`, `concat_ws`,
`length`, `abs`, `hex`, `pi`, `floor`, `ceil`, the transcendental math functions (`ln`,
`log`, `exp`, `acos`, `sin` and others, 5 uses or fewer each), `changes` (12), and the
window functions `rank` and `percent_rank`.

**Groups.** The cumulative clean cases when the model supports each group in turn:

| Group | Functions | Clean, cumulative |
|---|---|---|
| Core text and type functions | `typeof`, `length`, `octet_length`, `lower`, `upper`, `substr`, `instr`, `replace`, the `trim` family, `hex`, `unhex`, `quote`, `char`, `unicode`, `unistr`, `concat`, `concat_ws`, `ifnull`, `nullif`, `iif`, `if`, `likely`, `unlikely`, `likelihood`, scalar `min` and `max`, `abs`, `sign`, `zeroblob`, `like` and `glob` as functions, `sqlite_version` | 375 |
| Exact numeric functions | `round`, `floor`, `ceil`, `trunc`, `sqrt`, `pi`, `degrees`, `radians`, `mod` | 394 |
| `printf` and `format` | | 395 |
| JSON functions that build or edit text | `json_set`, `json_insert`, `json_replace`, `json_remove`, `json_patch`, `json_array`, `json_object`, `json_quote`, `json_error_position`, `json_pretty`, `json_group_array`, `json_group_object` | 515 |
| JSONB | `jsonb` and the `jsonb_*` functions | 685 |
| Aggregates | `group_concat`, `string_agg`, `total` | 692 |

The functions in no group (window functions, the transcendental math functions, `changes`
and the other connection functions, and names that are no function) appear in 58 clean
cases or fewer in total.

`DISTINCT` in a call appears in 57 out-of-scope cases. None of them is clean: each also uses
another feature, mostly a compound select or `EXPLAIN`.

## Native facts that the groups depend on

Checked with the pinned SQLite 3.51.0 build:

- The math functions are compiled in (`ln(2)` is `0.693147180559945`).
- An unknown name is the prepare error `no such function: nosuch`.
- `PRAGMA function_list` gives each built-in function with its number of arguments: 143
  names, 118 scalar and 27 aggregate or window (`min` and `max` are both).
- Scalar `min` and `max` compare under the collation of the left-most argument that has
  one: `min('B', 'a' COLLATE nocase)` is `a`.
- An argument that a JSON function gave is JSON: `json_array(json('[1]'))` is `[[1]]`, and
  `json_array('[1]')` is `["[1]"]`.
- `abs(-9223372036854775808)` fails while the statement runs with `integer overflow`.
- `likelihood(1, 2)` is the prepare error `second argument to likelihood() must be a
  constant between 0.0 and 1.0`.
- `lower` and `upper` change only ASCII letters (`lower('ÀB')` is `Àb`).
- `substr` and `length` count UTF-8 characters in text and bytes in a BLOB.
- `quote(1e300)` is `1.0e+300`, and `round(2.5)` is `3.0`.
- `jsonb('[1,2]')` is a BLOB in SQLite's binary JSON format.
