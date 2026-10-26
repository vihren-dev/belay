"""Native inputs for ordinary WITH definitions and their recursion boundary (ADR 0019, D5).

Each outcome is recorded from SQLite. The model must agree on supported uses and SQL
errors, and retain explicit restrictions for valid recursive queries and uncertain sources.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.authored_query_sources import TABLES
from conformance.authored_subqueries import COLUMN_TYPE, CORRELATED, SUBQUERY
from conformance.case_format import Json

WITH = "R-32586-01296"
"""The SELECT requirement allowing a WITH clause with common table expressions."""


def definitions() -> list[QueryCase]:
    """Names, per-use scope, metadata, unused templates, writes and recursive errors."""
    def case(name: str, sql: str, *features: str) -> QueryCase:
        """Reuse the source tables and attach the CTE and relevant column requirements."""
        return QueryCase("cte-" + name, TABLES, sql, (WITH, SUBQUERY, COLUMN_TYPE, CORRELATED),
                         ("common-table", *features))

    return [
        case("forward", "WITH a AS (SELECT * FROM b), b(x) AS (SELECT 3) SELECT * FROM a;", "forward"),
        case("reused", "WITH c(x) AS (SELECT 3) SELECT l.x,r.x FROM c l JOIN c r ON l.x=r.x;", "reused"),
        case("explicit-metadata", "WITH c(x,y,z) AS (SELECT a,b,c FROM t) SELECT x='A',y='1',z=1 FROM c WHERE y=1;", "affinity", "collation"),
        case("duplicate-columns", 'WITH c("true",x,x) AS (SELECT 1,2,3) SELECT * FROM c;', "names"),
        case("columns-do-not-alias-body", "WITH c(x) AS (SELECT y FROM (SELECT 1 AS y) WHERE x=1) SELECT * FROM c;", "error"),
        case("shadow-table", "WITH t(x) AS (SELECT 3) SELECT * FROM t;", "shadowing"),
        case("shadow-inner", "WITH a(x) AS (SELECT 1) SELECT (WITH a(x) AS (SELECT 2) SELECT x FROM a);", "shadowing"),
        case("lexical-definition", "WITH a AS (SELECT * FROM b), b AS (SELECT 1) SELECT * FROM (WITH b AS (SELECT 2) SELECT * FROM a);", "lexical"),
        case("shadow-self", "WITH a AS (WITH a AS (SELECT 5) SELECT * FROM a) SELECT * FROM a;", "shadowing"),
        case("per-use-outer", "WITH c AS (SELECT b) SELECT (SELECT * FROM c),(SELECT (SELECT * FROM c) FROM (SELECT 9 AS b)) FROM t WHERE b=1;", "outer"),
        case("per-use-outer-reversed", "WITH c AS (SELECT b) SELECT (SELECT (SELECT * FROM c) FROM (SELECT 9 AS b)),(SELECT * FROM c) FROM t WHERE b=1;", "outer"),
        case("sibling-error", "WITH c AS (SELECT t.b) SELECT * FROM t,c;", "scope", "error"),
        case("outer-beats-sibling", "WITH c AS (SELECT b) SELECT (SELECT c.b FROM (SELECT 9 AS b) d,c) FROM t WHERE b=1;", "outer"),
        case("unused-missing", "WITH c AS (SELECT * FROM missing) SELECT 1;", "unused"),
        case("unused-columns", "WITH c(x,y) AS (SELECT 1) SELECT 1;", "unused"),
        case("unused-cycle", "WITH c AS (SELECT * FROM c) SELECT 1;", "unused"),
        case("column-count", "WITH c(x,y) AS (SELECT 1) SELECT * FROM c;", "error"),
        case("function-call", "WITH c AS (SELECT 1) SELECT * FROM c(2);", "error"),
        case("circular", "WITH c AS (SELECT * FROM c) SELECT * FROM c;", "circular", "error"),
        case("indirect-cycle", "WITH a AS (SELECT * FROM b),b AS (SELECT * FROM a) SELECT * FROM a;", "circular", "error"),
        case("missing-before-cycle", "WITH c AS (SELECT * FROM missing,c) SELECT * FROM c;", "precedence", "error"),
        case("cycle-before-missing", "WITH c AS (SELECT * FROM c,missing) SELECT * FROM c;", "precedence", "error"),
        case("recursive", "WITH c(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM c WHERE x<3) SELECT * FROM c;", "recursive", "unmodeled"),
        case("recursive-empty-arguments", "WITH c(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM c() WHERE x<3) SELECT * FROM c;", "recursive", "unmodeled"),
        case("recursive-arguments", "WITH c(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM c(2) WHERE x<3) SELECT * FROM c;", "recursive", "unmodeled"),
        case("recursive-union", "WITH c(x) AS (SELECT 1 UNION SELECT x FROM c) SELECT * FROM c;", "recursive", "unmodeled"),
        case("recursive-inner-name", "WITH c(x) AS (WITH c(x) AS (SELECT 2) SELECT 1 UNION ALL SELECT x+1 FROM c WHERE x<3) SELECT * FROM c;", "recursive", "shadowing", "unmodeled"),
        case("recursive-two-sources", "WITH c(x) AS (SELECT 1 UNION ALL SELECT l.x FROM c l,c r) SELECT * FROM c;", "recursive", "error"),
        case("recursive-nested", "WITH c(x) AS (SELECT 1 UNION ALL SELECT (SELECT x FROM c)) SELECT * FROM c;", "recursive", "error"),
        case("recursive-extra-nested", "WITH c(x) AS (SELECT 1 UNION ALL SELECT (SELECT x FROM c) FROM c) SELECT * FROM c;", "recursive", "error"),
        case("recursive-column-count", "WITH c(x,y) AS (SELECT 1 UNION ALL SELECT x FROM c) SELECT * FROM c;", "recursive", "error"),
        case("recursive-arm-count", "WITH c(x) AS (SELECT 1 UNION ALL SELECT x,x FROM c) SELECT * FROM c;", "recursive", "error"),
        case("recursive-anchor-column", "WITH c(x) AS (SELECT missing UNION ALL SELECT x FROM c) SELECT * FROM c;", "recursive", "error"),
        case("recursive-arm-column", "WITH c(x) AS (SELECT 1 UNION ALL SELECT missing FROM c) SELECT * FROM c;", "recursive", "error"),
        case("recursive-aggregate", "WITH c(x) AS (SELECT 1 UNION ALL SELECT max(x) FROM c) SELECT * FROM c;", "recursive", "error"),
        case("recursive-order", "WITH c(x) AS (SELECT 1 UNION ALL SELECT x FROM c ORDER BY missing LIMIT 1) SELECT * FROM c;", "recursive", "error"),
        case("shadow-compound", "WITH c(x) AS (SELECT 1) SELECT x FROM c UNION ALL SELECT x FROM (WITH c(x) AS (SELECT 2) SELECT x FROM c) ORDER BY x;", "shadowing", "compound"),
        case("shadow-in-subquery", "WITH c(x) AS (SELECT 1) SELECT 2 IN (WITH c(x) AS (SELECT 2) SELECT x FROM c), 2 IN (SELECT x FROM c);", "shadowing", "in"),
        case("shadow-in-update", "WITH u(x) AS (SELECT 7) UPDATE t SET b=(SELECT x FROM u) WHERE b=1; SELECT b FROM t ORDER BY b;", "shadowing", "write"),
        case("shadow-insert-target", "WITH t(x) AS (SELECT 7) INSERT INTO t VALUES('q',(SELECT x FROM t),'z'); SELECT a,b,c FROM t ORDER BY b;", "shadowing", "write"),
        case("output-alias", "WITH c(x) AS (SELECT b FROM t) SELECT c.x AS y FROM c ORDER BY y;", "names"),
        case("materialized", "WITH c(x) AS MATERIALIZED (SELECT b FROM t) SELECT x FROM c ORDER BY x;", "hint", "unmodeled"),
        case("not-materialized", "WITH c(x) AS NOT MATERIALIZED (SELECT b FROM t) SELECT x FROM c ORDER BY x;", "hint", "unmodeled"),
        case("with-recursive-nonrecursive", "WITH RECURSIVE c(x) AS (SELECT 3) SELECT * FROM c;", "recursive", "unmodeled"),
        case("with-recursive-circular", "WITH RECURSIVE c AS (SELECT * FROM c) SELECT * FROM c;", "recursive", "unmodeled"),
        case("trigger-nested-select", "CREATE TRIGGER r AFTER INSERT ON e BEGIN SELECT (WITH c(x) AS (SELECT new.b) SELECT x FROM c); END; INSERT INTO e VALUES ('a',7); SELECT b FROM e;", "trigger"),
        case("trigger-nested-write", "CREATE TRIGGER r AFTER INSERT ON e BEGIN INSERT INTO u VALUES ('c',(WITH c(x) AS (SELECT new.b) SELECT x FROM c)); END; INSERT INTO e VALUES ('a',7); SELECT b FROM u WHERE a='c';", "trigger", "write", "unmodeled"),
        case("insert", "WITH c(x) AS (SELECT 7) INSERT INTO u VALUES ('c',(SELECT x FROM c)); SELECT b FROM u WHERE a='c';", "write"),
        case("update", "WITH c(x) AS (SELECT 7) UPDATE u SET b=(SELECT x FROM c); SELECT b FROM u;", "write"),
        case("delete", "WITH c(x) AS (SELECT 4) DELETE FROM u WHERE b=(SELECT x FROM c); SELECT a,b FROM u;", "write"),
        case("write-target", "WITH c AS (SELECT max(b) FROM u) UPDATE u SET b=(SELECT * FROM c);", "write", "unmodeled"),
        case("uncertain-membership", "WITH c AS (SELECT b FROM t LIMIT 1) SELECT * FROM c;", "unmodeled"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record the chosen CTE inputs with the existing native output recorder."""
    return query_records(definitions() if cases is None else cases, part="query-sources")
