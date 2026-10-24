"""CommonTables.lean keeps WITH definitions, their lexical parents and parameter numbers.

Resolution chooses a definition for each use; translation must keep unused definitions too.
The excluded keywords and SQLite parser-action errors retain their source ranges.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def test_with_definitions_keep_written_scopes_and_columns(parse_sql: Callable[..., Translation]) -> None:
    """Nested WITH names and forward references survive in the shared indexed syntax list."""
    [statement] = [item.value for item in parse_sql(
        'WITH a(x,y) AS (SELECT * FROM b), b AS (SELECT 1,2) '
        'SELECT (WITH a AS (SELECT 3) SELECT * FROM a),a.* FROM a;').statements()]
    query = statement['select']
    definitions = query['subqueries']
    assert [item['parent'] for item in definitions] == [None, None, None, 2]
    assert [item['commonTable'] for item in definitions] == [
        {'name': 'a', 'columns': ['x', 'y']}, {'name': 'b', 'columns': None},
        None, {'name': 'a', 'columns': None}]
    assert definitions[0]['source']['table'] == 'b'
    assert definitions[2]['source']['table'] == 'a'
    assert query['columns'][0]['expression']['value'] == {'subquery': {'index': 2}}


def test_with_parameters_include_unused_definitions(parse_sql: Callable[..., Translation]) -> None:
    """Unused CTE parameters still occupy their SQLite slots before the statement body."""
    [statement] = [item.value for item in parse_sql(
        'WITH unused AS (SELECT ?), c AS (SELECT ?5 AS x) SELECT ?,x FROM c;').statements()]
    query = statement['select']
    values = [item['columns'][0]['expression']['value'] for item in query['subqueries']]
    values.append(query['columns'][0]['expression']['value'])
    assert values == [{'parameter': {'number': number}} for number in (1, 5, 6)]


@pytest.mark.parametrize(('sql', 'form', 'field'), [
    ('WITH c AS (SELECT 1) INSERT INTO t VALUES ((SELECT * FROM c));', 'insert', 'rows'),
    ('WITH c AS (SELECT 1) UPDATE t SET x = (SELECT * FROM c);', 'update', 'assignments'),
    ('WITH c AS (SELECT 1) DELETE FROM t WHERE EXISTS (SELECT * FROM c);', 'delete', 'filter'),
])
def test_with_prefixes_supported_writes(parse_sql: Callable[..., Translation], sql: str, form: str, field: str) -> None:
    """Writes.lean retains a WITH definition and the write's ordinary scalar subquery."""
    [statement] = [item.value for item in parse_sql(sql).statements()]
    write = statement[form]
    assert field in write
    assert [item['parent'] for item in write['subqueries']] == [None, None]
    assert write['subqueries'][0]['commonTable'] == {'name': 'c', 'columns': None}
    assert write['subqueries'][1]['source']['table'] == 'c'


@pytest.mark.parametrize(('sql', 'refused'), [
    ('WITH RECURSIVE c AS (SELECT 1) SELECT * FROM c;', 'WITH RECURSIVE c AS (SELECT 1) SELECT * FROM c'),
    ('WITH c AS MATERIALIZED (SELECT 1) SELECT * FROM c;', 'AS MATERIALIZED'),
    ('WITH c AS NOT MATERIALIZED (SELECT 1) SELECT * FROM c;', 'AS NOT MATERIALIZED'),
])
def test_excluded_with_spellings_keep_ranges(parse_sql: Callable[..., Translation], sql: str, refused: str) -> None:
    """The chosen keyword and materialization exclusions remain explicit translation restrictions."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == 'UNSUPPORTED'
    assert sql.encode()[raised.value.start:raised.value.end].decode() == refused


@pytest.mark.parametrize(('sql', 'message'), [
    ('WITH a AS (SELECT 1), A AS (SELECT 2) SELECT 3;', 'duplicate WITH table name: A'),
    ('WITH c(x COLLATE nocase) AS (SELECT 1) SELECT * FROM c;', 'syntax error after column name'),
    ('WITH c(x DESC) AS (SELECT 1) SELECT * FROM c;', 'syntax error after column name'),
])
def test_with_parser_action_errors_are_input_errors(parse_sql: Callable[..., Translation], sql: str, message: str) -> None:
    """CommonTables.lean reproduces SQLite parser-action errors before model resolution."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == 'INPUT_ERROR'
    assert message in str(raised.value)
