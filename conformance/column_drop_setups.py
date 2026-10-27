"""The starting databases of the native cases of ALTER TABLE DROP COLUMN (ADR 0019, D4, part 3)."""

ROWS = (
    "CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT, c REAL, d INTEGER); CREATE INDEX ti ON t(c); "
    "INSERT INTO t VALUES(1,'p',1.5,10),(5,NULL,2.5,20),(9,'r',NULL,30); "
    "CREATE TABLE u(x INTEGER, b TEXT); INSERT INTO u VALUES(1,'m'),(2,'n');"
)
"""A table with a rowid alias, an index on one column and a gap in its rowids, and a second table that has a
column named `b` as well: a drop of `t.b` must leave `u.b` as it is."""
ROWIDS = (
    "CREATE TABLE r(x TEXT, y INTEGER, z TEXT); INSERT INTO r VALUES('a',1,'k'),('b',2,'l'),('c',3,'m'); "
    "DELETE FROM r WHERE y=2;"
)
"""A table with a rowid that is not a column and a gap in its rowids."""
KEYED = (
    "CREATE TABLE t(a INTEGER, b INTEGER UNIQUE CHECK (b > 0), c INTEGER GENERATED ALWAYS AS (a + 1) VIRTUAL, "
    "d TEXT, PRIMARY KEY (a)); INSERT INTO t(a,b,d) VALUES(1,2,'x'),(3,4,'y');"
)
"""A primary key, an inline UNIQUE column with its own CHECK, and a generated column that reads the key."""
VIEWED = (
    "CREATE TABLE t(a INTEGER, b TEXT, c INTEGER); INSERT INTO t VALUES(1,'p',7),(2,'q',8); "
    "CREATE VIEW v AS SELECT a, b FROM t;"
)
"""A view that reads two of the three columns."""
TRIGGERED = (
    "CREATE TABLE t(a INTEGER, b TEXT, c INTEGER); INSERT INTO t VALUES(1,'p',7); CREATE TABLE log(m TEXT); "
    "CREATE TRIGGER g AFTER INSERT ON t BEGIN INSERT INTO log VALUES(new.b); END;"
)
"""A trigger that reads one column of its table."""
INDEXED = (
    "CREATE TABLE t(a INTEGER, b INTEGER, c INTEGER); INSERT INTO t VALUES(1,2,3),(4,5,6); "
    "CREATE INDEX ti ON t(b); CREATE INDEX tp ON t(a) WHERE c > 0;"
)
"""An index on a column and a partial index whose filter reads another column."""
TABLE_RULES = (
    "CREATE TABLE t(a INTEGER, b INTEGER, c INTEGER, d INTEGER, CHECK (c > 0)); INSERT INTO t VALUES(1,2,3,4);"
)
"""A table-level CHECK that reads one column."""
TABLE_KEYS = (
    "CREATE TABLE t(a INTEGER, b INTEGER, c INTEGER, UNIQUE (b)); INSERT INTO t VALUES(1,2,3);"
)
"""A table-level UNIQUE key."""
READER = (
    "CREATE TABLE t(a INTEGER, b INTEGER, c INTEGER GENERATED ALWAYS AS (b + 1) VIRTUAL); INSERT INTO t(a,b) VALUES(1,2);"
)
"""A generated column that reads another column."""
GENERATED_ONLY = "CREATE TABLE t(a INTEGER, b INTEGER AS (5)); INSERT INTO t(a) VALUES(1);"
"""A table whose only other column is generated."""
TWO_CHECKS = (
    "CREATE TABLE t(a INTEGER CHECK (a > 0), b INTEGER, CHECK (A > 0)); INSERT INTO t VALUES(1,2);"
)
"""A CHECK constraint of the column, which goes with it, and a CHECK of the table that reads it under another letter case."""
CHILD = (
    "CREATE TABLE p(id INTEGER PRIMARY KEY, extra TEXT); INSERT INTO p VALUES(1,'x'),(2,'y'); "
    "CREATE TABLE c(id INTEGER PRIMARY KEY, pid INTEGER, note TEXT, FOREIGN KEY (pid) REFERENCES p(id)); "
    "INSERT INTO c VALUES(10,1,'n');"
)
"""A parent with a column that no key names, and a child with a table-level foreign key."""
