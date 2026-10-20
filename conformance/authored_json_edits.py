"""Authored coverage cases of the JSON functions that build or edit text (ADR 0015, slice 3).

The cases follow the "Tests" list of the slice 3 task: `json_quote`, `json_array`,
`json_object`, `json_set`, `json_insert`, `json_replace`, `json_remove`, `json_patch`,
`json_pretty` and `json_error_position` over SQL values of each type, the JSON subtype of
their arguments, the aggregates `json_group_array` and `json_group_object`, and the argument
errors in queries without FROM. Native SQLite is the only
source of outcomes. SQLite's JSON documentation (`json1.html`) has no requirement marks, so the
cases name the requirement of the result columns of a simple SELECT. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE j(k INTEGER PRIMARY KEY, d TEXT, v, p TEXT); "
          "INSERT INTO j VALUES(1, '{\"a\":1,\"b\":[1,2]}', 7, '$.a'), "
          "(2, '[1,{\"c\":null}]', 2.5, '$[#]'), (3, '\"x\"', 'a\"b', '$.b[1]'), "
          "(4, NULL, NULL, NULL), (5, ' {\"a\" : {\"b\":1}} ', '[3]', '$.a.b');")
"""One table with JSON text (one NULL, one with white space), values of each type except BLOB,
and paths."""

GROUPS = ("CREATE TABLE g(k INTEGER PRIMARY KEY, grp INTEGER, label, v, w TEXT); "
          "INSERT INTO g VALUES (1, 1, 'a', 1, '[1]'), (2, 1, NULL, 2, '{}'), (3, 1, 3, 'x', 'true'), "
          "(4, 2, 'b', NULL, '\"s\"'), (5, 2, 'b', 2.5, '[2,3]'), (6, 1, 1.5, '[1]', 'null');")
"""One table for the aggregates: two groups, labels of each type with one NULL and one
repeated, values of each type, and JSON text."""

RESULTS = "R-08669-22397"
"""SQLite: a simple SELECT returns one column for each result expression. The JSON functions
have no requirement marks of their own."""


def definitions() -> list[QueryCase]:
    """The coverage cases of slice 3 of ADR 0015."""
    case = QueryCase
    return [
        case("json-build-array-quote", TABLES, "SELECT k, json_array(k, v, d, NULL, 1e300, -0.0), json_quote(v), "
             "json_quote(d), json_array() FROM j ORDER BY k;", (RESULTS,), ("functions", "json_array", "json_quote")),
        case("json-build-object", TABLES, "SELECT k, json_object('k', k, 'v', v, 'd', d, 'k', 1.5), json_object() "
             "FROM j ORDER BY k;", (RESULTS,), ("functions", "json_object")),
        case("json-build-subtype", TABLES, "SELECT k, json_array(json(d), json_extract(d, '$.b'), "
             "json_extract(d, '$.a'), json_extract(d, '$.a', '$.b'), d -> '$', d ->> '$', json_quote(json(d)), "
             "+json_array(1), json_pretty(d)) FROM j WHERE k = 1 OR k = 2 OR k = 5 ORDER BY k;", (RESULTS,),
             ("functions", "json_array", "subtype")),
        case("json-edit-set", TABLES, "SELECT k, json_set(d, p, v), json_set(d, '$.z', json('[1]'), '$.z[#]', 2), "
             "json_set(d, '$', v), json_set(d, NULL, 1, '$[0]', 9) FROM j WHERE k <> 3 ORDER BY k;", (RESULTS,),
             ("functions", "json_set")),
        case("json-edit-insert-replace", TABLES, "SELECT k, json_insert(d, p, v), json_replace(d, p, v), "
             "json_insert(d, '$.a', 0, '$.n.m', 1), json_replace(d, '$', 0) FROM j WHERE k <> 3 ORDER BY k;",
             (RESULTS,), ("functions", "json_insert", "json_replace")),
        case("json-edit-remove", TABLES, "SELECT k, json_remove(d, p), json_remove(d, '$.b[0]', '$.a'), "
             "json_remove(d, '$'), json_remove(d), json_remove(d, '$[0]', NULL) FROM j WHERE k <> 3 ORDER BY k;",
             (RESULTS,), ("functions", "json_remove")),
        case("json-edit-patch", TABLES, "SELECT k, json_patch(d, '{\"a\":null,\"b\":{\"x\":1},\"n\":{\"m\":null}}'), "
             "json_patch(d, '[1]'), json_patch('{\"a\":{\"b\":1,\"c\":2}}', d) FROM j WHERE k <> 3 ORDER BY k;",
             (RESULTS,), ("functions", "json_patch")),
        case("json-edit-pretty-position", TABLES, "SELECT k, json_pretty(d), json_pretty(d, '--'), "
             "json_pretty(d, NULL), json_error_position(d) FROM j WHERE k <> 3 ORDER BY k;", (RESULTS,),
             ("functions", "json_pretty", "json_error_position")),
        case("json-build-object-label", TABLES, "SELECT json_object('a', 1, 2, 3);", (RESULTS,),
             ("functions", "json_object", "error")),
        case("json-build-object-count", TABLES, "SELECT json_object('a', 1, 'b');", (RESULTS,),
             ("functions", "json_object", "error")),
        case("json-edit-even-count", TABLES, "SELECT json_insert('{}', '$.a');", (RESULTS,),
             ("functions", "json_insert", "error")),
        case("json-edit-bad-path", TABLES, "SELECT json_set('{}', 'a', 1);", (RESULTS,),
             ("functions", "json_set", "error")),
        case("json-edit-in-writes", TABLES, "UPDATE j SET d = json_set(d, '$.w', k) WHERE k = 1 OR k = 5; "
             "INSERT INTO j(k, d) VALUES (6, json_object('n', json_array(1, 'x'))); SELECT k, d FROM j ORDER BY k;",
             (RESULTS,), ("functions", "json_set", "update")),
        case("json-group-aggregates", GROUPS, "SELECT grp AS n, json_group_array(v), json_group_object(label, v), "
             "json_group_array(json(w)), json_group_object(label, json_extract(w, '$')) FROM g GROUP BY grp "
             "ORDER BY n;", (RESULTS,), ("functions", "json_group_array", "json_group_object", "group-by")),
        case("json-group-whole-table", GROUPS, "SELECT json_group_array(k), json_group_object(w, k) FROM g; "
             "SELECT json_group_array(v), json_group_object(label, v), count(*) FROM g WHERE k > 9;", (RESULTS,),
             ("functions", "json_group_array", "json_group_object", "empty-table")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `json-edits`."""
    return query_records(definitions() if cases is None else cases, part="json-edits")
