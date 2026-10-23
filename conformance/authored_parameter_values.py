"""Authored cases of the numbers and values of parameters (outcomes 2, 3 and 4 of
plans/20261023-parameters.task.md).

The numbering cases bind a different value to each number, so that a wrong number gives a wrong
row. The cases of the places put a parameter in each place of an expression that resolution
accepts. The affinity and collation cases compare a parameter with literals and columns. The
cases of `ORDER BY ?` and `GROUP BY ?` bind an integer that names a result column. `ORDER BY ?1`
makes every row a tie, so each row may be the one that `LIMIT 1` keeps; `ORDER BY 1` keeps only the
smallest value, which SQLite's row is not. The parameter is also a result column, so that the
recorder can observe the ties.
"""

from conformance.authored_parameters import NULL, ParameterCase, integer, real, text

TABLE = ("CREATE TABLE t(id INTEGER PRIMARY KEY, k TEXT, n INTEGER); "
         "INSERT INTO t VALUES(1, 'c', 30), (2, 'a', 10), (3, 'b', 20);")
"""Three rows whose order of insertion is not the order of `k` or `n`."""
UPSERT = "CREATE TABLE u(k TEXT PRIMARY KEY, v TEXT); INSERT INTO u VALUES('a', 'old');"
"""A table with a key that an upsert can hit."""
TRIGGER = ("CREATE TABLE p(a); CREATE TABLE log(x); "
           "CREATE TRIGGER p_log AFTER INSERT ON p BEGIN INSERT INTO log VALUES(new.a * 2); END;")
"""A table whose insert trigger writes a value of the new row to `log`."""
AFFINITY = "CREATE TABLE a(t TEXT, i INTEGER, b BLOB, c TEXT COLLATE NOCASE); INSERT INTO a VALUES('2', 2, 2, 'a');"
"""Columns with TEXT, INTEGER and no affinity, and a NOCASE column."""

NUMBERED = "R-33509-39458"
"""SQLite: ?NNN holds a spot for the NNN-th parameter."""
NEXT_NUMBER = "R-33670-36097"
"""SQLite: ? has one more than the largest parameter number already assigned."""
NAMED = "R-11370-04520"
"""SQLite: a named parameter gets one more than the largest number already assigned."""
SAME_NAME = "R-52009-56800"
"""SQLite: the later uses of a name have the number of its first use."""
COLON, AT, DOLLAR = "R-11620-22743", "R-49783-61279", "R-62610-51329"
"""SQLite: the parameter forms :AAAA, @AAAA and $AAAA."""
BIND = "R-25857-01867"
"""SQLite: the values of parameters are set with the sqlite3_bind routines."""
COMPARE = "R-12881-55998"
"""SQLite: the comparison rules of storage classes."""


def numbering_cases() -> list[ParameterCase]:
    """The numbering of outcome 2: each number has its own value."""
    case = ParameterCase
    values = tuple(integer(10 * index) for index in range(1, 10))
    return [
        case("parameter-numbers-mixed", "", "SELECT ?, ?5, ?, :a, @a, $a, :a;",
             (NUMBERED, NEXT_NUMBER, NAMED, SAME_NAME, COLON, AT, DOLLAR), ("numbering", "mixed-forms"), (values,)),
        case("parameter-numbers-leading-zero", "", "SELECT ?01, ?, ?3;", (NUMBERED, NEXT_NUMBER),
             ("numbering", "leading-zero"), ((integer(1), integer(2), integer(3)),)),
        case("parameter-numbers-name-after-number", "", "SELECT ?3, :x, ?1, :x, ?;", (NUMBERED, NAMED, SAME_NAME),
             ("numbering", "named-after-numbered"), (values[:5],)),
        case("parameter-numbers-repeated-name", "", "SELECT :a + 1 AS one, :b, :a * 2 AS two, @a;",
             (NAMED, SAME_NAME, AT), ("numbering", "repeated-name"), ((integer(5), integer(7), integer(9)),)),
        case("parameter-numbers-name-forms", "", "SELECT :1, @1, $a::b, $a(x), :1a;", (COLON, AT, DOLLAR),
             ("numbering", "name-forms"), (values[:5],)),
        case("parameter-numbers-each-statement", "",
             "SELECT ?, ?; SELECT ?2, ?; SELECT :a, ?1; SELECT 'none';",
             (NEXT_NUMBER, NUMBERED, NAMED), ("numbering", "script", "per-statement-values"),
             ((integer(1), integer(2)), (integer(3), integer(4), integer(5)), (integer(6),), ())),
    ]


def place_cases() -> list[ParameterCase]:
    """A parameter in each place of outcome 3."""
    case = ParameterCase
    return [
        case("parameter-place-result-where", TABLE, "SELECT ?1 AS p, n FROM t WHERE n > ?2 ORDER BY n;", (BIND,),
             ("place", "result-column", "where"), ((text("p"), integer(15)),)),
        case("parameter-place-values-set-delete", TABLE,
             "INSERT INTO t VALUES(?, ?, ?) RETURNING id, k, n; UPDATE t SET n = ?1 + n, k = ?2 WHERE id = ?3 RETURNING n, k;"
             "DELETE FROM t WHERE n = ? RETURNING id; SELECT id, k, n FROM t ORDER BY id;",
             (BIND,), ("place", "values", "set", "delete", "returning"),
             ((integer(4), text("d"), integer(40)), (integer(5), text("z"), integer(2)), (integer(10),), ())),
        case("parameter-place-upsert", UPSERT,
             "INSERT INTO u VALUES(?1, ?2) ON CONFLICT(k) DO UPDATE SET v = ?3 || excluded.v WHERE ?4 RETURNING k, v;"
             "INSERT INTO u VALUES(?1, ?2) ON CONFLICT(k) DO UPDATE SET v = ?3 WHERE ?4 RETURNING k, v;",
             (BIND,), ("place", "upsert", "returning"),
             ((text("a"), text("new"), text("set-"), integer(1)), (text("a"), text("x"), text("y"), integer(0)))),
        case("parameter-place-trigger-write", TRIGGER, "INSERT INTO p VALUES(?1); INSERT INTO p VALUES(?); SELECT x FROM log ORDER BY x;",
             (BIND,), ("place", "trigger", "values"), ((integer(21),), (text("4"),), ())),
        case("parameter-place-functions-case", "",
             "SELECT abs(?1), coalesce(?2, 'none'), CASE ?3 WHEN 1 THEN 'one' ELSE 'other' END, "
             "CASE WHEN ?4 THEN 'yes' ELSE 'no' END, ?5 BETWEEN 1 AND 3, ?5 IN (?1, 2), ?6 LIKE 'a%', CAST(?6 AS INTEGER);",
             (BIND,), ("place", "function-arguments", "case", "between", "in", "like", "cast"),
             ((integer(-4), NULL, integer(1), integer(0), integer(2), text("abc")),)),
        case("parameter-place-subqueries", TABLE,
             "SELECT (SELECT count(*) FROM t WHERE n > ?1) AS c, n FROM t "
             "WHERE n IN (SELECT n FROM t WHERE n < ?2) AND EXISTS (SELECT 1 WHERE ?3) ORDER BY n;",
             (BIND,), ("place", "subquery", "in-subquery", "exists"), ((integer(10), integer(30), integer(1)),)),
        case("parameter-place-join-group-having", TABLE,
             "SELECT x.id AS a, y.id AS b FROM t AS x JOIN t AS y ON y.n = x.n + ?1 ORDER BY a;"
             "SELECT n % ?1 AS g, count(*) AS c FROM t GROUP BY g HAVING count(*) > ?2 ORDER BY g;",
             (BIND,), ("place", "join-on", "group-by-expression", "having"),
             ((integer(10),), (integer(20), integer(0)))),
    ]


def comparison_cases() -> list[ParameterCase]:
    """The affinity and collation examples of outcome 3, and outcome 4."""
    case = ParameterCase
    return [
        case("parameter-no-affinity", "", "SELECT ?1 = '2', ?1 = 2, ?2 = 2, ?2 = '2', ?3 = 2;", (COMPARE,),
             ("affinity", "literal"), ((integer(2), text("2"), real(2.0)),)),
        case("parameter-column-affinity", AFFINITY, "SELECT t = ?1, i = ?2, b = ?2, ?1 = t, ?2 = i FROM a;", (COMPARE,),
             ("affinity", "column"), ((integer(2), text("2")),)),
        case("parameter-insert-affinity", AFFINITY,
             "INSERT INTO a VALUES(?1, ?2, ?3, ?4) RETURNING typeof(t), typeof(i), typeof(b), c;", (COMPARE,),
             ("affinity", "insert"), ((integer(3), text("3"), text("3"), text("B")),)),
        case("parameter-collation", AFFINITY,
             "SELECT ?1 = 'A', ?1 COLLATE NOCASE = 'A', c = ?1, ?1 = c, ?2 = c FROM a;", (COMPARE,),
             ("collation",), ((text("a"), text("A")),)),
        case("parameter-order-by", TABLE, "SELECT n, ?1 FROM t ORDER BY ?1; SELECT n, ?1 FROM t ORDER BY ?1 LIMIT 1; SELECT n FROM t ORDER BY 1;",
             ("R-29779-04281",), ("order-by", "constant", "column-number", "limit"), ((integer(1),), (integer(1),), ())),
        case("parameter-group-by", TABLE,
             "SELECT count(*) AS c, max(n) AS m FROM t GROUP BY ?1; SELECT count(*) AS c FROM t WHERE 0 GROUP BY ?1;",
             ("R-02223-49279",), ("group-by", "constant", "empty-result"), ((integer(2),), (integer(1),))),
    ]


def value_definitions() -> list[ParameterCase]:
    """The cases of outcomes 2, 3 and 4."""
    return numbering_cases() + place_cases() + comparison_cases()
