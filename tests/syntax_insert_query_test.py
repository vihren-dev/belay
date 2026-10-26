"""The translation maps INSERT from a query (`packages/belay-sqlite-text/Belay/Sqlite/Translation/Writes.lean`,
`insertQuery`, through the text package's program; ADR 0019, D4).

These tests check the JSON that Lean's `Syntax.Statement.insertSelect` and `Syntax.SelectBody` decoders
read: the table, the optional column list, the query as a body whose subqueries are the subqueries of
the query, the conflict clauses, the algorithm and RETURNING. An INSERT of VALUES rows keeps its
`insert` form. `tests/surface/TranslationChecks.lean` checks the source ranges of the paths.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]

def parameter(number: int) -> dict[str, object]:
    """The JSON of a numbered parameter."""
    return {"parameter": {"number": number}}


SOURCE_TABLE = {"table": "s", "alias": None, "arguments": None, "query": None, "schema": None}
"""The source `s` as a plain table reference."""


def insert_select_of(parse_sql: Callable[..., Translation], sql: str) -> dict[str, object]:
    """The fields of the INSERT from a query of one statement."""
    [statement] = [item.value for item in parse_sql(sql).statements()]
    assert isinstance(statement, dict)
    return statement["insertSelect"]


def test_plain_query_is_a_body(parse_sql: Callable[..., Translation]) -> None:
    """The query is a select body with its source, no conflicts and no algorithm."""
    insert = insert_select_of(parse_sql, "INSERT INTO t SELECT x FROM s;")
    assert insert["table"] == "t"
    assert (insert["columns"], insert["conflicts"], insert["algorithm"]) == (None, [], None)
    assert insert["source"]["source"] == SOURCE_TABLE
    assert (insert["source"]["subqueries"], insert["source"]["compound"]) == ([], None)


def test_column_list_algorithm_and_replace(parse_sql: Callable[..., Translation]) -> None:
    """The column list keeps its names; OR IGNORE and REPLACE INTO give their algorithms."""
    ignore = insert_select_of(parse_sql, "INSERT OR IGNORE INTO t(a, b) SELECT x, y FROM s;")
    assert (ignore["columns"], ignore["algorithm"]) == (["a", "b"], "ignore")
    replace = insert_select_of(parse_sql, "REPLACE INTO t SELECT x FROM s;")
    assert replace["algorithm"] == "replace"


def test_compound_query_lists_its_terms(parse_sql: Callable[..., Translation]) -> None:
    """A compound query has a compound field and its terms as subqueries of the body."""
    source = insert_select_of(parse_sql, "INSERT INTO t SELECT x FROM s UNION ALL SELECT y FROM s;")["source"]
    assert source["compound"] == {"first": 0, "rest": [["unionAll", 1]]}
    assert len(source["subqueries"]) == 2


def test_with_prefix_definition_is_a_subquery(parse_sql: Callable[..., Translation]) -> None:
    """A WITH definition of the statement is a subquery of the body."""
    source = insert_select_of(parse_sql, "WITH c(x) AS (SELECT 1) INSERT INTO t SELECT x FROM c;")["source"]
    assert len(source["subqueries"]) == 1


def test_conflict_clause_after_a_filter(parse_sql: Callable[..., Translation]) -> None:
    """SQLite's grammar needs a WHERE before ON CONFLICT of an INSERT from a query."""
    insert = insert_select_of(parse_sql, "INSERT INTO t SELECT x FROM s WHERE true ON CONFLICT DO NOTHING;")
    assert insert["conflicts"] == [{"target": None, "action": "nothing"}]
    assert insert["source"]["filter"] is not None


def test_returning_columns_are_a_field(parse_sql: Callable[..., Translation]) -> None:
    """RETURNING columns are the `returning` field of the statement, as with VALUES rows."""
    insert = insert_select_of(parse_sql, "INSERT INTO t SELECT x FROM s RETURNING a;")
    assert len(insert["returning"]) == 1


def test_values_rows_keep_the_insert_form(parse_sql: Callable[..., Translation]) -> None:
    """INSERT of VALUES is still `insert`."""
    [statement] = [item.value for item in parse_sql("INSERT INTO t VALUES (1);").statements()]
    assert "insert" in statement


def test_parameters_are_numbered_in_text_order(parse_sql: Callable[..., Translation]) -> None:
    """Parameters of the query and of RETURNING are numbered in text order."""
    insert = insert_select_of(parse_sql, "INSERT INTO t SELECT x FROM s WHERE y = ? RETURNING ?;")
    assert insert["source"]["filter"]["compare"]["right"] == parameter(1)
    assert insert["returning"][0]["expression"]["value"] == parameter(2)


def test_conflict_clause_right_after_from_is_a_parser_error(parse_sql: Callable[..., Translation]) -> None:
    """SQLite's grammar reads `ON` after `FROM s` as the start of a join constraint, so the pinned parser
    refuses the text; the translation reports its message and does not decide otherwise."""
    with pytest.raises(SqlError) as raised:
        parse_sql("INSERT INTO t SELECT x FROM s ON CONFLICT DO NOTHING;").statements()
    assert raised.value.status == "INPUT_ERROR"
