# Conformance case format

ADR 0004's test-only `conformance-runner` accepts one JSON object per line and
returns one result per line. The current case format is version 3. Versions 1
and 2 carried statements and schemas that Python resolved; ADR 0008 replaced
them, and the runner refuses them. Frozen corpus records are not cases: they keep
SQL text and native observations, and replay builds a version 3 case from them
each time.

`packages/belay-sqlite/Belay/Sqlite/Codec.lean` and
`packages/belay-sqlite/Belay/Sqlite/Codec/Resolution.lean` own the codecs for
values, statement syntax and catalogs. `VerifierConformance/Json.lean` adds the case
and observation records. The Python side is `belay/sqlite/syntax.py` for statement
syntax, `conformance/native_metadata.py` for native tables and
`conformance/case_format.py` for values and rows. ADR 0003's `verify-bundle` uses
the same syntax codec for its structural record (see the
[data path guide](data-path.md)).

## Record

| Field | Meaning |
| --- | --- |
| `version` | Integer `3`. Other versions are harness errors. |
| `release`, `sourceId` | The SQLite release and build. The runner resolves under the documented profile of this release. |
| `schemaSql`, `migrationSql` | Original SQL, kept separately. |
| `schema`, `script` | Statement syntax of the schema and migration SQL, as `belay.sqlite.syntax` maps them. |
| `initial` | Native tables before the migration. |
| `nativeTrace` | Initial observation, then one observation per executed statement. |
| `requirements` | Array of requirement-ID strings; `[]` when there are none. |
| `provenance` | Array of `[key, value]` string pairs, including fixture name and engine source ID. |
| `outputs`, `parameters` | Statement outputs and their bound parameters ([outputs](conformance-format-v2.md)); `null` and `[]` when the record has no outputs. |

Statement syntax uses Lean's derived JSON encoding of `Syntax.Statement`: nullary
constructors are strings (`"begin"`, `"commit"`, `"rollback"`), and other
constructors are single-key objects with named fields, for example
`{"addColumn": {"table": "t", "column": {"name": "c", "declaredType": "TEXT", "constraints": []}}}`.
Names keep their case as written. Numeric literals keep their token text.

A native table has `name` (as written in `sqlite_schema`), `columns`,
`primaryKey`, `uniqueKeys`, `indexes` and `rows`. Each column has `name`,
`declaredType` (the declared type text, `""` for none), `notNull` and
`defaultValue` (the default's text or null), from `PRAGMA table_xinfo`. The
primary key lists column positions in key order. `uniqueKeys` lists the key
positions of each UNIQUE constraint index (`index_list` origin `u`). `indexes`
lists the explicit indexes (origin `c`) with `name`, `columns` and `unique`. Rows
have integer `rowid` and ordered `values`.

Values preserve storage classes:

```json
["null", {"integer":{"value":-4}}, {"real":{"bits":"4609434218613702656"}},
 {"text":{"bytes":[99,97,102,195,169]}}, {"blob":{"bytes":[0,255]}}]
```

REAL payloads are unsigned 64-bit decimal **strings**, avoiding JSON consumers'
floating-point precision loss. Bytes are integers in 0..255. Physical rowids are
signed 64-bit integers; duplicate table names (after ASCII folding), duplicate
rowids, and incorrect row widths are rejected by the decoder. Native
initialization failures are harness errors. Fixture setup binds REAL values
through the C API: infinities survive, while NaN becomes native NULL and
disagrees with a requested NaN REAL in the initial-state comparison.

## Observations

An observation contains `visible`, `persisted` (native table arrays),
`transactionOpen`, `primaryCode`, and `extendedCode`. Code zero means success.
While a transaction is open, `persisted` is read on a second connection. Otherwise
it is the same snapshot as `visible`. Both codes are retained, and the decoder
requires `extendedCode % 256 == primaryCode`.

The model compares **primary** codes: success 0, `constraintViolation` 19, and
other modeled errors, including SQLite's prepare errors, 1. Extended codes remain
diagnostics because the model does not distinguish constraint subtypes. Error
messages are not compared. `unmodeled` is unsupported admission, not a native
error.

## Comparison

The runner resolves `schema` in description mode and `script` in execution mode
(`resolveSchemaAndScript`). A model restriction is `MODEL_UNSUPPORTED`. A schema
that SQLite ran but resolution refuses is a disagreement at the initial state.
The runner then follows the catalog after each statement and compares, under the
visible and the committed catalog:

- each catalog table with the native table of the same folded name: its name as
  written, its columns, primary key, UNIQUE constraint keys and explicit indexes
  (`VerifierConformance.Native.tablesMatch`);
- the rows of the model table at that catalog position with the native rows, in
  rowid order;
- that no native table is outside the catalog.

This comparison checks the catalog that resolution computes. Python reads the
native metadata only; it does not resolve the schema.

## Evidence boundary

`classifyCase` compares the initial states, checks production admission, then
compares every reached observation. Missing or extra observations disagree.
`DISAGREE` has a zero-based statement `position`, or null for an initial mismatch.
`MODEL_UNSUPPORTED` can never satisfy `checkCase`. Syntax without a statement
constructor is refused before a Lean case exists. Native observation and decoding
failures report `HARNESS_ERROR`; the checker is not invoked on failed native
acquisition.

The runner trusts that the syntax was mapped and observations were acquired by the
harness. Supplying a fabricated JSON trace does not establish native evidence.
`--emit-lean` returns the decoded record and its closed Lean term. Kernel
regressions first use `#guard` to verify the elaborated term re-encodes to the
original case JSON, then prove `checkCase fixture = true` with
`decide +kernel`; there is no second Python comparator or source emitter for SQL.
Axiom audits reject `sorryAx`, `ofReduceBool`, and `_native` names.

The final observation of the model trace is proved equal to observing `runSql`.
This is a model theorem, not a proof about the C library, codec, or harness.
