# Task: an example of data loss that depends on row values (split by age)

Created 2026-11-19 (status: `20261119-null-split-example.status.md`).
Status: in progress.

## Problem

A reader asked: does Belay catch data loss that depends on specific row values, not only on the
schema? The README example loses rows for a reason of the schema (foreign keys). This task adds an
example where the loss depends on a value in a row: a NULL age.

Schema `shop`:

```sql
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);
```

Migration `splitByAge`: it creates `minors` and `adults`, copies the customers with `age < 18` and
`age >= 18`, drops `customers` and creates the view `customers` as the `UNION ALL` of the two
tables, in one transaction. On native SQLite 3.51.0 every statement succeeds, and a customer whose
age is NULL is lost: neither condition is true for NULL.

The fixed migration `splitByAgeFixed` copies the NULL ages into `adults`
(`WHERE age >= 18 OR age IS NULL`). Every value that is not NULL makes exactly one of `age < 18` and
`age >= 18` true, because SQLite compares every two values that are not NULL, so the two copies
together hold each customer once.

## What must be true when the task is done

- A surface fixture in `tests/surface` states the schema, the two migrations and the read
  `allCustomers` (`SELECT id, name, age FROM customers`, without `ORDER BY`).
- `#sql_check splitByAge preserves allCustomers on shop` answers `false`. The counterexample has a
  customer whose age is NULL, and the answer has a replay script for native SQLite.
- The fixture keeps the counterexample as a `db!` database and states, with `decide +kernel`, that
  on it every statement of `splitByAge` succeeds and the read loses the customer, and that
  `splitByAgeFixed` keeps the customer.
- `theorem … : splitByAgeFixed preserves allCustomers on shop`, with a kernel-checked proof that uses
  only the axioms `propext`, `Classical.choice` and `Quot.sound`; also
  `splitByAgeFixed succeeds on shop` if its cost is reasonable.
- The example code is in `tests/surface`. A general law that the proof needs goes into the package,
  with a plain-words docstring and a proof sketch.

## Tests

- A Python test compiles the fixture, asserts the false answer of the check, its NULL age and its
  replay, and audits the `#print axioms` reports (only the three logical axioms, no `sorry`).
- When native `sqlite3` is present, the test runs the replay script and checks that SQLite loses the
  customer too.

## Tricky points

- Result order: an unordered `SELECT` gives its rows in the normal form (`Resolved.normalForm`, a
  sort by `compareRows`), so the read through the view compares as a multiset of rows; `ORDER BY` is
  not needed. A proof needs that the normal form of two permutations of the same rows is the same
  list, which the package does not yet state.
- The read after the migration goes through a view over a `UNION ALL`. The read certificate
  (`ReadCertificate`, `preservesAt`) covers only reads of one table, so the proof cannot use it as
  it is. The general part of `ReadCertificate.preservesAt` (equal step outputs on every branch give
  preservation) can be stated without the certificate.
- The two `INSERT … SELECT` statements make the migration a program with branches; a proof must
  cover every branch in which the migration succeeds (`sendStatements_branch_invariant`), as the
  table-rebuild proof in `examples/table-rebuild/Proof` does.
- The model has no step law for `CREATE VIEW` yet.
- The default time limit of `#sql_check` is 10 s of wall-clock time, and one existing test is flaky
  under load (issue #426). The fixture keeps the schema small and sets `sql.checkTimeLimit` when the
  default is not enough.
