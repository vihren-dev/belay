"""Views.lean preserves unresolved definitions, field order and SQL source ranges.

The model checks parameters and resolves names later; translation must retain both.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def test_create_view_keeps_definition_and_written_columns(parse_sql: Callable[..., Translation]) -> None:
    """CREATE translation retains explicit names and defers absent-source lookup."""
    sql = '  CREATE VIEW IF NOT EXISTS [Mixed V]("α",b) AS SELECT x,y FROM missing;'
    [statement] = parse_sql(sql).statements()
    view = statement.value['createView']
    assert (view['name'], view['ifNotExists'], view['columns']) == ('Mixed V', True, ['α', 'b'])
    assert view['query']['source']['table'] == 'missing'
    assert len(view['query']['columns']) == 2
    assert view['subqueries'] == []
    assert sql.encode()[statement.start:statement.end].decode() == sql.strip().removesuffix(';')
    [plain] = parse_sql('CREATE VIEW v AS SELECT 1;').statements()
    assert plain.value['createView']['columns'] is None
    assert plain.value['createView']['ifNotExists'] is False


def test_create_view_retains_all_parameter_slots(parse_sql: Callable[..., Translation]) -> None:
    """Unused CTE and scalar-subquery parameters survive for the model's native error."""
    [statement] = parse_sql(
        'CREATE VIEW v AS WITH unused AS (SELECT ?5) SELECT ?, (SELECT ?);').statements()
    view = statement.value['createView']
    root = view['query']['columns'][0]['expression']['value']
    nested = [item['columns'][0]['expression']['value'] for item in view['subqueries']]
    assert [root, *nested] == [{'parameter': {'number': n}} for n in (6, 5, 7)]


@pytest.mark.parametrize(('sql', 'refused'), [
    ('CREATE TEMP VIEW v AS SELECT 1;', 'TEMP'),
    ('CREATE VIEW main.v AS SELECT 1;', '.v'),
])
def test_create_view_schema_boundaries(parse_sql: Callable[..., Translation], sql: str, refused: str) -> None:
    """Views.lean rejects only the excluded temp/schema component at its original range."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == 'UNSUPPORTED'
    assert sql.encode()[raised.value.start:raised.value.end].decode() == refused


@pytest.mark.parametrize('suffix', ['COLLATE nocase', 'DESC'])
def test_view_column_parser_actions(parse_sql: Callable[..., Translation], suffix: str) -> None:
    """The reused column-list translator preserves SQLite's action-time syntax error."""
    with pytest.raises(SqlError) as raised:
        parse_sql(f'CREATE VIEW v(x {suffix}) AS SELECT 1;').statements()
    assert raised.value.status == 'INPUT_ERROR'
    assert 'syntax error after column name' in str(raised.value)
