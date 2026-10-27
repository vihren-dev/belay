"""The starting databases of the native cases of ALTER TABLE RENAME TO and RENAME COLUMN (ADR 0019, D4)."""

TABLES = (
    "CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT COLLATE NOCASE, c REAL); CREATE INDEX ti ON t(b); "
    "CREATE TABLE u(x INTEGER, b TEXT); INSERT INTO t VALUES(1,'p',1.5),(5,'Q',2.5); "
    "INSERT INTO u VALUES(1,'m'),(2,'n');"
)
"""A table with a rowid alias, a NOCASE column and an index on it, and a second table that has a column
named `b` as well: a rename of `t.b` must leave `u.b` as it is."""
ROWIDS = (
    "CREATE TABLE r(x TEXT, y INTEGER); INSERT INTO r VALUES('a',1),('b',2),('c',3); DELETE FROM r WHERE y=2;"
)
"""A table with a rowid that is not a column and a gap in its rowids."""
DEPENDENTS = (
    "CREATE TABLE t(a INTEGER, b TEXT); INSERT INTO t VALUES(1,'p'),(2,'q'); CREATE TABLE log(m TEXT); "
    "CREATE VIEW v AS SELECT a, b AS label, 'b' AS text FROM t WHERE b <> 'z'; "
    "CREATE TRIGGER g AFTER INSERT ON t BEGIN INSERT INTO log VALUES(new.b); END;"
)
"""A view and a trigger that read the columns of `t`, one of them also as a string that is not a name."""
CONSTRAINTS = (
    "CREATE TABLE t(a INTEGER, b INTEGER UNIQUE CHECK (b > 0), c INTEGER GENERATED ALWAYS AS (a + b) VIRTUAL, "
    "PRIMARY KEY (a), CHECK (a < b + 100)); CREATE INDEX ti ON t(b, a) WHERE a > 0; "
    "INSERT INTO t(a,b) VALUES(1,2),(3,4);"
)
"""Constraints, a generated column and a partial index that name the columns of `t`."""
KEYS = (
    "CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT UNIQUE); INSERT INTO p VALUES(1,'x'),(2,'y'); "
    "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INTEGER REFERENCES p(id) ON DELETE CASCADE, "
    "pname TEXT REFERENCES p(name)); INSERT INTO c VALUES(10,1,'x'),(11,2,'y');"
)
"""A parent table with a key and a unique column, and a child table that refers to both."""
