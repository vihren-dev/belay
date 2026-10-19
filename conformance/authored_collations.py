"""Authored coverage cases of collations (ADR 0014, slice 3).

The cases follow the "Tests" list of the slice 3 task: `NOCASE` and `RTRIM` comparisons,
including the bytes that `NOCASE` does not fold and a tab after `RTRIM`; the collation of a
comparison by SQLite's rules (an explicit `COLLATE` on the left, then on the right, then the
column on the left, then on the right); `ORDER BY`, `GROUP BY`, `min` and `max` over a
`NOCASE` column and under an explicit `COLLATE`; a `NOCASE` UNIQUE column, an index term
with `COLLATE`, the collations of index columns in the catalog, a `NOCASE` primary key of a
`WITHOUT ROWID` table, the equality of `USING`, and the prepare error of an unknown name in a
column definition and an index term. An unknown name elsewhere is a model restriction
(`unknown-collation`), whose example is in `conformance.restriction_examples`.
Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE c(n TEXT COLLATE NOCASE, r TEXT COLLATE RTRIM, b TEXT); "
          "CREATE TABLE w(n TEXT, b TEXT); "
          "CREATE TABLE u(k TEXT COLLATE NOCASE UNIQUE, v INTEGER); "
          "CREATE TABLE p(k TEXT COLLATE NOCASE PRIMARY KEY, v INTEGER) WITHOUT ROWID; "
          "CREATE TABLE x(k TEXT, v INTEGER); "
          "INSERT INTO c VALUES('a', 'a ', 'a'), ('B', 'b', 'B'), ('A', 'a', 'a'), ('Ä', 'a\t', 'ä'); "
          "INSERT INTO w VALUES('a', 'b'); INSERT INTO u VALUES('a', 1); "
          "INSERT INTO p VALUES('b', 1), ('A', 2), ('c', 3); INSERT INTO x VALUES('z', 1);")
"""A table with a `NOCASE`, an `RTRIM` and a `BINARY` column whose rows differ only by case,
trailing spaces, a tab and a non-ASCII capital; a table without collations for `USING`; a
`NOCASE` UNIQUE column; a `WITHOUT ROWID` table with a `NOCASE` key in another order than
inserted; and a table without collations for indexes."""

BUILT_IN = "R-02402-03425"
"""SQLite: there are three built-in collating functions: BINARY, NOCASE and RTRIM."""
NOCASE = "R-34481-43669"
"""SQLite: NOCASE folds the ASCII capitals A to Z into lowercase; only ASCII is folded."""
ASCII_ONLY = "R-38980-08445"
"""SQLite: NOCASE does not implement a general purpose unicode caseless comparison."""
RTRIM = "R-31624-24737"
"""SQLite: RTRIM is like BINARY except that trailing spaces do not change the result."""
COLUMN_DEFAULT = "R-55061-47754"
"""SQLite: the COLLATE clause of a column gives the column's default collation sequence."""
EXPLICIT = "R-29702-55194"
"""SQLite: an explicit COLLATE of an operand is used, with precedence to the left operand."""
COLUMN_OPERAND = "R-11423-52711"
"""SQLite: else a column operand's collation is used, with precedence to the left operand."""
OVERRIDES = "R-58731-25439"
"""SQLite: the COLLATE operator overrides the collation of a column definition."""
NAME_CASE = "R-04232-24861"
"""SQLite: collation names that compare equal by sqlite3_strnicmp() are the same name."""
POSTFIX = "R-59577-33471"
"""SQLite: COLLATE is a unary postfix operator that assigns a collating sequence."""
SAME_AFFINITY = "R-22414-48736"
"""SQLite: a COLLATE operator has the affinity of its left operand."""
ORDER_COLUMN = "R-05898-54598"
"""SQLite: an ORDER BY term that is a column sorts with the column's collation."""
ORDER_EXPLICIT = "R-64199-22471"
"""SQLite: an ORDER BY term with a COLLATE operator sorts with that collation."""
ORDER_ALIAS = "R-09398-26102"
"""SQLite: an ORDER BY alias of an expression with COLLATE sorts with that collation."""
GROUP_BY = "R-10470-30318"
"""SQLite: GROUP BY compares text values by the usual rules of collation selection."""
TEXT_COMPARE = "R-16735-29088"
"""SQLite: two TEXT values compare with an appropriate collating sequence."""
INDEX_COLUMN = "R-57195-25932"
"""SQLite: an index uses its column's collation unless CREATE INDEX gives a COLLATE."""
INDEX_XINFO = "R-15313-19540"
"""SQLite: index_xinfo gives the name of the collating sequence of each index column."""
USING_LEFT = "R-38422-04402"
"""SQLite: the left column of a join is the left operand of its equality for collation."""


def definitions() -> list[QueryCase]:
    """The coverage cases of collations."""
    case = QueryCase
    return [
        case("collate-nocase-column", TABLES, "SELECT b FROM c WHERE n = 'a';", (NOCASE, COLUMN_DEFAULT),
             ("collation", "nocase", "comparison")),
        case("collate-column-right", TABLES, "SELECT b FROM c WHERE 'a' = n;", (COLUMN_OPERAND,),
             ("collation", "nocase", "comparison")),
        case("collate-column-left", TABLES, "SELECT n, b FROM c WHERE b = n;", (COLUMN_OPERAND,),
             ("collation", "binary", "comparison")),
        case("collate-explicit-right", TABLES, "SELECT n, b FROM c WHERE b = n COLLATE NOCASE;", (EXPLICIT, POSTFIX),
             ("collation", "explicit", "comparison")),
        case("collate-explicit-left", TABLES, "SELECT n, b FROM c WHERE n COLLATE BINARY = b COLLATE NOCASE;",
             (EXPLICIT, OVERRIDES), ("collation", "explicit", "comparison")),
        case("collate-through-plus-cast", TABLES,
             "SELECT b FROM c WHERE +n = 'a'; SELECT b FROM c WHERE CAST(n AS TEXT) = 'a'; "
             "SELECT b FROM c WHERE +(b COLLATE NOCASE) = 'B';", (COLUMN_OPERAND, EXPLICIT),
             ("collation", "unary-plus", "cast")),
        case("collate-name-case", TABLES, "SELECT n FROM c WHERE b = n COLLATE \"NoCase\";", (NAME_CASE,),
             ("collation", "name")),
        case("collate-nocase-ascii-only", TABLES, "SELECT b FROM c WHERE n = 'ä';", (ASCII_ONLY, NOCASE),
             ("collation", "nocase", "non-ascii")),
        case("collate-rtrim", TABLES, "SELECT b FROM c WHERE r = 'a'; SELECT b FROM c WHERE r = 'a   ';", (RTRIM,),
             ("collation", "rtrim", "comparison")),
        case("collate-rtrim-order", TABLES, "SELECT r, n FROM c ORDER BY r, n COLLATE BINARY;", (RTRIM, ORDER_COLUMN),
             ("collation", "rtrim", "order-by")),
        case("collate-value-classes", TABLES,
             "SELECT 1 COLLATE NOCASE = 1, 'a' COLLATE NOCASE = 'A', 'a' = 'A' COLLATE RTRIM, "
             "'a ' = 'a' COLLATE RTRIM;",
             (TEXT_COMPARE, BUILT_IN), ("collation", "fromless")),
        case("collate-affinity", TABLES, "SELECT k FROM x WHERE v COLLATE NOCASE = '1';", (SAME_AFFINITY,),
             ("collation", "affinity")),
        case("collate-order-column", TABLES, "SELECT n FROM c ORDER BY n;", (ORDER_COLUMN,),
             ("collation", "nocase", "order-by")),
        case("collate-order-explicit", TABLES, "SELECT n FROM c ORDER BY n COLLATE BINARY DESC;", (ORDER_EXPLICIT,),
             ("collation", "explicit", "order-by")),
        case("collate-order-alias", TABLES, "SELECT b COLLATE NOCASE AS m FROM c ORDER BY m;", (ORDER_ALIAS,),
             ("collation", "explicit", "order-by", "alias")),
        case("collate-group-by", TABLES,
             "SELECT count(*) FROM c GROUP BY n ORDER BY 1; "
             "SELECT count(*) FROM c GROUP BY b COLLATE NOCASE ORDER BY 1;",
             (GROUP_BY,), ("collation", "group-by")),
        case("collate-group-by-value", TABLES,
             "SELECT n, count(*) FROM c GROUP BY n ORDER BY 2, 1; SELECT b, count(*) FROM c GROUP BY b COLLATE NOCASE "
             "ORDER BY 2, 1;", (GROUP_BY,), ("collation", "group-by", "grouping-value")),
        case("collate-min-max", TABLES, "SELECT min(n), max(n), min(b), min(b COLLATE NOCASE) FROM c;", (TEXT_COMPARE,),
             ("collation", "aggregate")),
        case("collate-unique-column", TABLES, "INSERT INTO u VALUES('A', 2);", (COLUMN_DEFAULT, INDEX_COLUMN),
             ("collation", "unique", "constraint")),
        case("collate-upsert", TABLES,
             "INSERT INTO u VALUES('A', 5) ON CONFLICT(k) DO UPDATE SET v = excluded.v; SELECT k, v FROM u;",
             (COLUMN_DEFAULT,), ("collation", "unique", "on-conflict")),
        case("collate-index-term", TABLES,
             "CREATE UNIQUE INDEX xk ON x(k COLLATE NOCASE); INSERT INTO x VALUES('Z', 2);",
             (INDEX_COLUMN,), ("collation", "index", "constraint")),
        case("collate-index-catalog", TABLES, "CREATE INDEX ci ON c(n, b COLLATE RTRIM, r, +b COLLATE nocase);",
             (INDEX_COLUMN, INDEX_XINFO), ("collation", "index", "catalog")),
        case("collate-without-rowid", TABLES, "SELECT k FROM p; INSERT INTO p VALUES('C', 4);", (COLUMN_DEFAULT,),
             ("collation", "without-rowid", "scan", "constraint")),
        case("collate-using", TABLES,
             "SELECT count(*) FROM c JOIN w USING(n); SELECT count(*) FROM w JOIN c USING(n);", (USING_LEFT,),
             ("collation", "using")),
        case("collate-unknown-index", TABLES, "CREATE INDEX ci ON c(n COLLATE foo);", (BUILT_IN,),
             ("collation", "index", "prepare-error")),
        case("collate-add-column", TABLES,
             "ALTER TABLE x ADD COLUMN t TEXT COLLATE NOCASE; INSERT INTO x VALUES('y', 2, 'A'); "
             "SELECT k FROM x WHERE t = 'a';", (COLUMN_DEFAULT,), ("collation", "add-column")),
        case("collate-unknown-column", TABLES, "CREATE TABLE y(a TEXT COLLATE foo);", (BUILT_IN,),
             ("collation", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `collations`."""
    return query_records(definitions() if cases is None else cases, part="collations")
