"""The starting databases of the native cases of INSERT from a query (ADR 0019, D4, amended 2026-10-25)."""

TABLES = (
    "CREATE TABLE s(a INTEGER, b TEXT); INSERT INTO s VALUES(1,'x'),(2,'y'),(3,'z'); "
    "CREATE TABLE t(a INTEGER, b TEXT); "
    "CREATE TABLE k(id INTEGER PRIMARY KEY, v TEXT UNIQUE); INSERT INTO k VALUES(10,'y'); "
    "CREATE TABLE e(a INTEGER, b TEXT);"
)
"""A source with three rows, an empty target, a target with a rowid alias and a unique column
that holds one row, and an empty source."""
INDEXED = (
    "CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER); CREATE INDEX sx ON s(x); "
    "INSERT INTO s VALUES(1,20),(2,10); CREATE TABLE t(id INTEGER PRIMARY KEY, name INTEGER);"
)
"""A source with an index on `x`, whose rows 20 and 10 are in the opposite order of the index."""
OVERFLOW = (
    "CREATE TABLE t(id INTEGER PRIMARY KEY); CREATE TABLE u(id INTEGER PRIMARY KEY); INSERT INTO u VALUES(5); "
    "CREATE TABLE s(x INTEGER); INSERT INTO s VALUES(5),(-9223372036854775808);"
)
"""A target, a target that already holds the first row, and a source with a row and then the smallest
integer, whose `abs` overflows. The last row inserted is the second row of the source, so that a
statement that writes the row 5 and then fails shows whether it wrote before it failed."""

TWO_ORDERS = (
    "CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER); CREATE INDEX sx ON s(x); INSERT INTO s VALUES(1,20),(2,10); "
    "CREATE TABLE t(x INTEGER); CREATE TABLE log(id INTEGER PRIMARY KEY, x INTEGER); "
    "CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES(new.x); END;"
)
"""A source that SQLite may read by its scan or by an index, and a target whose trigger logs each row."""

PRECEDENCE = (
    "CREATE TABLE src(x INTEGER); INSERT INTO src VALUES(2),(1),(-9223372036854775808); "
    "CREATE TABLE dest(x INTEGER UNIQUE); INSERT INTO dest VALUES(1);"
)
"""Source rows 2, 1 and the smallest integer, and a unique destination that holds 1."""
SORTED = (
    "CREATE TABLE src(id INTEGER PRIMARY KEY, x INTEGER, k INTEGER); "
    "INSERT INTO src VALUES(1,2,1),(2,1,2),(3,-9223372036854775808,3); "
    "CREATE TABLE dest(x INTEGER UNIQUE); INSERT INTO dest VALUES(1);"
)
"""Source rows ordered by `k`, and a unique destination that holds 1."""
TRIGGERED = (
    "CREATE TABLE s(a INTEGER, b TEXT); INSERT INTO s VALUES(1,'x'),(2,'y'); "
    "CREATE TABLE t(a INTEGER UNIQUE, b TEXT); CREATE TABLE log(x);"
)
"""A source, a unique target and a log table that triggers write."""
TRANSFER = (
    "CREATE TABLE s(a INTEGER UNIQUE); CREATE TABLE t(a INTEGER UNIQUE); "
    "INSERT INTO s VALUES(10),(20),(30); DELETE FROM s WHERE a=20;"
)
"""A source and a target with the same index, whose source rowids are 1 and 3."""
KEYS = (
    "CREATE TABLE p(id INTEGER PRIMARY KEY); INSERT INTO p VALUES(1),(2); "
    "CREATE TABLE c(id INTEGER PRIMARY KEY, p INTEGER REFERENCES p(id) ON DELETE CASCADE); "
    "CREATE TABLE s(a INTEGER); INSERT INTO s VALUES(1),(2),(3);"
)
"""A parent with two rows, a child with a cascade, and a source with a missing parent."""
SHAPES = (
    "CREATE TABLE s(a INTEGER, b TEXT); INSERT INTO s VALUES(1,'x'),(2,'y'); "
    "CREATE TABLE g(a INTEGER, b TEXT DEFAULT 'd', c INTEGER AS (a*2), d INTEGER DEFAULT 7); "
    "CREATE TABLE w(a INTEGER PRIMARY KEY, b TEXT) WITHOUT ROWID;"
)
"""A source, a target with a default and a generated column, and a WITHOUT ROWID target."""
