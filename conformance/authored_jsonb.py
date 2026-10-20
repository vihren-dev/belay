"""Authored coverage cases of JSONB (ADR 0015, slice 4).

The cases follow the "Tests" list of the slice 4 task: the JSONB of each node type and header
size, each `jsonb_*` function, JSONB as an argument of the JSON functions that give text, a
BLOB that is not JSONB read as text, the error of a BLOB that is not JSONB as a stored value,
`json_valid` flags on BLOBs, `json_each` over JSONB, the JSONB aggregates, and JSONB in table
cells. Native SQLite is the only source of outcomes. SQLite's JSON documentation
(`json1.html`) has no requirement marks, so the cases name the requirement of the result
columns of a simple SELECT. The cases use `conformance.authored_queries.QueryCase` and its
recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE b(k INTEGER PRIMARY KEY, j BLOB, t TEXT); "
          "INSERT INTO b VALUES(1, x'8b133117613c176200', '{\"a\":[1,2],\"s\":\"x\"}'), "
          "(2, x'5b315d', '[3]'), (3, NULL, NULL), (4, x'cc0d176bab01020035312e30232d32', 'true');")
"""One table with JSONB cells (one canonical array, one BLOB that is JSON text, one canonical
object), JSON text and NULL."""

GROUPS = ("CREATE TABLE g(k INTEGER PRIMARY KEY, grp INTEGER, label TEXT, v); "
          "INSERT INTO g VALUES (1, 1, 'a', 1), (2, 1, 'b', 'x\"y'), (3, 2, 'c', 2.5), (4, 2, NULL, NULL);")
"""One table for the JSONB aggregates: two groups, text with a double quote, and NULL."""

RESULTS = "R-08669-22397"
"""SQLite: a simple SELECT returns one column for each result expression. The JSON functions
have no requirement marks of their own."""

LONG = "x" * 300
"""A string of 300 bytes, which needs a JSONB header with two size bytes."""


def definitions() -> list[QueryCase]:
    """The coverage cases of slice 4 of ADR 0015."""
    case = QueryCase
    return [
        case("jsonb-encodings", TABLES, "SELECT jsonb('[1,\"a\",{\"b\":null}]'), jsonb('0x1F'), jsonb('{a:1}'), "
             "jsonb('.5'), jsonb('Infinity'), jsonb('NaN'), jsonb('+5'), jsonb('-0'), jsonb('\"a\\nb\"'), "
             "jsonb('\"a\\x41\"'), jsonb('1.5E+10'), jsonb(' [ ] '), jsonb(NULL), jsonb(7), jsonb(2.5);",
             (RESULTS,), ("functions", "jsonb")),
        case("jsonb-header-sizes", TABLES, f"SELECT jsonb_array(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1), jsonb('\"{LONG}\"'), "
             f"jsonb_array('{LONG}', '{LONG}'), length(jsonb('\"{LONG}\"'));", (RESULTS,),
             ("functions", "jsonb", "header")),
        case("jsonb-extract", TABLES, "SELECT k, jsonb_extract(t, '$.a'), jsonb_extract(t, '$.s'), "
             "jsonb_extract(t, '$.a[0]', '$.a'), jsonb_extract(j, '$'), jsonb_extract(t, '$.z') FROM b ORDER BY k;",
             (RESULTS,), ("functions", "jsonb_extract")),
        case("jsonb-build", TABLES, "SELECT jsonb_array(1, 2.5, 'a\"b', NULL, json('[2]'), jsonb('[3]')), "
             "jsonb_object('a', 1, 'b', jsonb('{\"c\":true}'), 'd', 'x'), jsonb_array(), jsonb_object();",
             (RESULTS,), ("functions", "jsonb_array", "jsonb_object")),
        case("jsonb-edit", TABLES, "SELECT k, jsonb_set(t, '$.n', 'a\"b'), jsonb_insert(t, '$.a[#]', 9), "
             "jsonb_replace(t, '$.s', json('[1]')), jsonb_remove(t, '$.a[0]'), "
             "jsonb_patch(t, '{\"s\":null,\"z\":{\"w\":1}}'), jsonb_set(j, '$[#]', jsonb('{\"q\":1}')) FROM b "
             "ORDER BY k;", (RESULTS,), ("functions", "jsonb_set", "jsonb_insert", "jsonb_replace", "jsonb_remove",
                                          "jsonb_patch")),
        case("jsonb-as-argument", TABLES, "SELECT k, json(j), json_extract(j, '$[2].b'), json_type(j), "
             "json_array_length(j), j -> '$[1]', j ->> '$[1]', json_set(j, '$[0]', 5), json_valid(j, 4), "
             "json_valid(j, 8), json_valid(j, 1) FROM b ORDER BY k;",
             (RESULTS,), ("functions", "jsonb", "blob-argument")),
        case("jsonb-blob-as-text", TABLES, "SELECT json(x'5b315d'), json_extract(x'7b7d', '$'), "
             "json_valid(x'5b315d'), json_valid(x'5b315d', 4), json_valid(x'1331', 1), json_valid(x'232d61', 8);",
             (RESULTS,), ("functions", "blob-argument")),
        case("jsonb-blob-value", TABLES, "SELECT json_array(x'abcd');", (RESULTS,),
             ("functions", "json_array", "error")),
        case("jsonb-blob-set-value", TABLES, "SELECT json_set('[1]', '$[0]', x'5b315d');", (RESULTS,),
             ("functions", "json_set", "error")),
        case("jsonb-each", TABLES, "SELECT b.k, e.key, e.value, e.type, e.id, e.json FROM b, "
             "json_each(b.j) AS e WHERE b.k = 1 ORDER BY e.id;", (RESULTS,), ("functions", "json_each", "jsonb")),
        case("jsonb-group-aggregates", GROUPS, "SELECT grp AS n, jsonb_group_array(v), jsonb_group_object(label, v) "
             "FROM g GROUP BY grp ORDER BY n;", (RESULTS,),
             ("functions", "jsonb_group_array", "jsonb_group_object", "group-by")),
        case("jsonb-in-writes", TABLES, "UPDATE b SET j = jsonb_set(jsonb(t), '$.w', k) WHERE k = 1 OR k = 4; "
             "INSERT INTO b(k, j) VALUES (5, jsonb_object('n', jsonb_array(1, 'x'))); "
             "SELECT k, j, json(j) FROM b ORDER BY k;", (RESULTS,), ("functions", "jsonb_set", "update")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `jsonb`."""
    return query_records(definitions() if cases is None else cases, part="jsonb")
