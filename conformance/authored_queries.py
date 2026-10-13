"""Authored coverage cases of single-table queries (ADR 0012, slice 1, "Testing").

For each query rule: a case where it applies, a neighbor where it does not, and the
boundary values that ADR 0012 lists: integer and real ties, the storage-class order
of NULL, numbers, text and blobs, NULL in each operand, an empty table with and
without `GROUP BY`, a `LIMIT` that cuts a tie group, and each prepare error. Native
SQLite is the only source of outcomes: these are inputs, recorded as version 5
records with statement outputs. An ordered query projects its sort keys, so that
the recorder can observe complete tie groups.
"""

from dataclasses import dataclass

from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql

TABLE = ("CREATE TABLE t(k, v TEXT, n INTEGER); INSERT INTO t VALUES(NULL, 'a', 1), (2, 'B', 2), "
         "(1.5, 'b', NULL), ('x', 'c', 3), (X'01', 'a', 4), (2.0, NULL, 5);")
"""A table with each storage class in the untyped column `k`, an integer and a real
that are equal, text that differs only in case, and NULL in each column."""
EMPTY = "CREATE TABLE e(k, n INTEGER);"
"""A table without rows."""
LARGE = "CREATE TABLE r(x); INSERT INTO r VALUES(9007199254740992.0), (9007199254740993);"
"""A REAL and an integer that differ by one but have the same nearest double."""


@dataclass(frozen=True)
class QueryCase:
    """One coverage case: setup and query SQL, the requirement identifiers it covers, and
    descriptive features."""

    name: str
    setup: str
    sql: str
    requirements: tuple[str, ...]
    features: tuple[str, ...]


def definitions() -> list[QueryCase]:
    """The coverage cases: each rule, its neighbor, its boundary values and its errors."""
    case = QueryCase
    return [
        case("order-storage-classes", TABLE, "SELECT k FROM t ORDER BY k;",
             ("R-12881-55998", "R-14505-63184", "R-64324-28127"), ("order-by", "storage-class", "numeric-tie")),
        case("order-descending", TABLE, "SELECT k FROM t ORDER BY k DESC;", ("R-06617-54588",),
             ("order-by", "descending")),
        case("order-ascending-default", TABLE, "SELECT n FROM t ORDER BY n ASC;", ("R-18705-33393",),
             ("order-by", "neighbor")),
        case("order-by-alias-and-number", TABLE, "SELECT v AS label, n FROM t ORDER BY label, 2 DESC;",
             ("R-29779-04281", "R-53528-47027"), ("order-by", "alias", "result-number")),
        case("compare-null-operands", TABLE,
             "SELECT k, k = NULL, NULL <> k, k IS NULL, k IS NOT NULL, NULL IS NULL FROM t;",
             ("R-24731-45773", "R-06325-15315", "R-19812-36779", "R-24392-63621"), ("comparison", "null")),
        case("filter-keeps-true-rows", TABLE, "SELECT v FROM t WHERE k = k;", ("R-60775-64916",),
             ("where", "null")),
        case("filter-logic", TABLE, "SELECT n FROM t WHERE n > 1 AND NOT n = 4 OR v IS NULL;",
             ("R-60775-64916",), ("where", "and", "or", "not")),
        case("three-valued-logic", TABLE,
             "SELECT n, n > 2 AND k IS NOT NULL, n > 2 OR k > 1, NOT n > 2 FROM t;", ("R-24392-63621",),
             ("and", "or", "not", "null")),
        case("integer-real-exact", LARGE, "SELECT count(*) FROM r WHERE x = 9007199254740993;",
             ("R-12881-55998",), ("comparison", "integer-real")),
        case("integer-real-order", LARGE, "SELECT x FROM r ORDER BY x DESC;", ("R-12881-55998",),
             ("order-by", "integer-real")),
        case("text-binary", TABLE, "SELECT v FROM t WHERE v = 'b';", ("R-53528-47027",),
             ("comparison", "binary-collation")),
        case("text-binary-order", TABLE, "SELECT v FROM t ORDER BY v;", ("R-53528-47027", "R-12881-55998"),
             ("order-by", "binary-collation")),
        case("blob-above-text", TABLE, "SELECT k FROM t WHERE k > 'x';", ("R-64324-28127", "R-13324-20915"),
             ("comparison", "storage-class")),
        case("count-skips-null", TABLE, "SELECT count(k), count(v), count(n), count(*) FROM t;",
             ("R-34280-42283", "R-13776-21310"), ("count", "null")),
        case("min-max-skip-null", TABLE, "SELECT min(n), max(n), min(v), max(k), min(k) FROM t;",
             ("R-16028-39081", "R-52585-35928"), ("min", "max", "null")),
        case("aggregate-empty-table", EMPTY, "SELECT count(*), count(k), min(n), max(n) FROM e;",
             ("R-64138-28774",), ("count", "min", "max", "empty-table")),
        case("group-by-empty-table", EMPTY, "SELECT k, count(*) FROM e GROUP BY k;", ("R-02223-49279",),
             ("group-by", "empty-table", "neighbor")),
        case("group-by-null-equal", TABLE, "SELECT v, count(*), min(n) FROM t GROUP BY v;",
             ("R-14926-50129", "R-02223-49279"), ("group-by", "null")),
        case("group-by-numeric-tie", TABLE, "SELECT k, count(*) FROM t GROUP BY k ORDER BY 1;",
             ("R-14926-50129", "R-12881-55998"), ("group-by", "numeric-tie")),
        case("limit-cuts-tie", TABLE, "SELECT v FROM t ORDER BY v LIMIT 3;", ("R-37911-51642",),
             ("limit", "tie-group")),
        case("limit-offset", TABLE, "SELECT n FROM t ORDER BY n LIMIT 2 OFFSET 1;", ("R-20467-43422",),
             ("limit", "offset")),
        case("limit-comma-offset", TABLE, "SELECT n FROM t ORDER BY n LIMIT 1, 2;",
             ("R-19509-40356", "R-33788-46243"), ("limit", "offset")),
        case("limit-negative", TABLE, "SELECT n FROM t ORDER BY n LIMIT -1 OFFSET 4;", ("R-03014-26414",),
             ("limit", "offset", "negative")),
        case("limit-zero", TABLE, "SELECT n FROM t LIMIT 0;", ("R-37911-51642",), ("limit", "empty-result")),
        case("result-names", TABLE, "SELECT N, v AS Label, n  =  1, * FROM t WHERE n = 1;",
             ("R-17768-43126",), ("result-names",)),
        case("no-such-column", TABLE, "SELECT missing FROM t;", ("R-44050-47362",), ("prepare-error",)),
        case("no-such-column-folded-neighbor", TABLE, "SELECT V FROM t WHERE N = 2;", ("R-44050-47362",),
             ("ascii-folding", "neighbor")),
        case("no-such-table", TABLE, "SELECT * FROM missing;", ("R-44050-47362",), ("prepare-error",)),
        case("aggregate-in-where", TABLE, "SELECT count(*) FROM t WHERE count(*) > 1;", ("R-20637-43463",),
             ("prepare-error", "misuse")),
        case("aggregate-in-aggregate", TABLE, "SELECT max(min(n)) FROM t;", ("R-20637-43463",),
             ("prepare-error", "misuse")),
        case("aggregate-in-group-by", TABLE, "SELECT count(*) FROM t GROUP BY 1;", ("R-20637-43463",),
             ("prepare-error", "group-by")),
        case("aggregate-written-in-group-by", TABLE, "SELECT n FROM t GROUP BY max(n);", ("R-20637-43463",),
             ("prepare-error", "group-by")),
        case("order-by-out-of-range", TABLE, "SELECT n FROM t ORDER BY 2;", ("R-29779-04281",),
             ("prepare-error", "order-by")),
        case("order-by-in-range-neighbor", TABLE, "SELECT n FROM t ORDER BY 1 DESC;", ("R-29779-04281",),
             ("order-by", "neighbor")),
        case("group-by-out-of-range", TABLE, "SELECT n FROM t GROUP BY 0;", ("R-02223-49279",),
             ("prepare-error", "group-by")),
        case("missing-column-and-order-range", TABLE, "SELECT missing FROM t ORDER BY 5;", ("R-44050-47362",),
             ("prepare-error", "two-errors")),
    ]


def records(cases: list[QueryCase] | None = None, part: str = "queries") -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, under SQLite's default
    measured profile, with the part and its features."""
    selected = definitions() if cases is None else cases
    measured = profile(())
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=measured),
             "part": part, "features": list(case.features)}
            for case in selected]
