"""The translation numbers the parameters of each statement as SQLite does
(`packages/belay-sqlite-text/Belay/Sqlite/Translation/Parameters.lean`, through the text
package's program).

These tests check the numbers that the JSON of `Syntax.Expr.parameter` carries for each token
form, the numbering of each statement apart from the others, and the refusals with SQLite's
messages for the numbers and the forms that SQLite refuses while it parses (ADR 0019, D1).
The numbers and messages were checked with native SQLite 3.51.0.
"""

from collections.abc import Callable

import pytest
from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation


pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def numbers(translation: Translation) -> list[list[object]]:
    """The values of the result columns of each SELECT statement."""
    return [[column["expression"]["value"] for column in item.value["select"]["columns"]]
            for item in translation.statements()]


def parameter(number: int) -> dict[str, object]:
    """The JSON of a parameter with its number."""
    return {"parameter": {"number": number}}


def test_numbers_follow_sqlite_for_each_form(parse_sql: Callable[..., Translation]) -> None:
    """`?` takes one more than the largest number so far, `?NNN` takes NNN, and a name takes
    the number of its first use; `:a`, `@a`, `$a` and `#a` are different names."""
    [values] = numbers(parse_sql("SELECT ?, ?5, ?, :a, @a, $a, :a, #a, ?01;"))
    assert values == [parameter(number) for number in [1, 5, 6, 7, 8, 9, 7, 10, 1]]


def test_names_take_sqlite_token_forms(parse_sql: Callable[..., Translation]) -> None:
    """`:1`, `@1`, `:1a`, `$a::b` and `$a(x)` are names, and a name used again has its first
    number."""
    [values] = numbers(parse_sql("SELECT :1, @1, :1a, $a::b, $a(x), :1;"))
    assert values == [parameter(number) for number in [1, 2, 3, 4, 5, 1]]


def test_each_statement_numbers_its_own_parameters(parse_sql: Callable[..., Translation]) -> None:
    """The numbers start again in each statement."""
    assert numbers(parse_sql("SELECT ?, :a; SELECT :a, ?;")) == [
        [parameter(1), parameter(2)], [parameter(1), parameter(2)]]


def test_numbers_follow_the_text_in_subqueries_and_returning(parse_sql: Callable[..., Translation]) -> None:
    """The numbers follow the order of the text, also in a subquery, which the translation maps
    after the statement's own clauses, and in RETURNING."""
    [select, insert] = [item.value for item in parse_sql(
        "SELECT (SELECT ?2) WHERE ?; INSERT INTO t VALUES (?) RETURNING ?;").statements()]
    assert select["select"]["filter"] == parameter(3)
    assert select["select"]["subqueries"][0]["columns"][0]["expression"]["value"] == parameter(2)
    assert insert["insert"]["rows"] == [[parameter(1)]]
    assert insert["insert"]["returning"][0]["expression"]["value"] == parameter(2)


def test_default_of_a_parameter_reaches_the_model(parse_sql: Callable[..., Translation]) -> None:
    """`DEFAULT (?)` is a default with the parameter, for which the model gives SQLite's error;
    another expression in parentheses stays refused."""
    [table] = [item.value for item in parse_sql("CREATE TABLE d(a DEFAULT (?));").statements()]
    assert table["createTable"]["columns"][0]["constraints"] == [{"default": {"value": parameter(1), "sourceText": "?"}}]
    with pytest.raises(SqlError) as raised:
        parse_sql("CREATE TABLE d(a DEFAULT (1));").statements()
    assert raised.value.status == "UNSUPPORTED"


@pytest.mark.parametrize(("sql", "token", "message"), [
    ("SELECT 1, ?0;", "?0", "variable number must be between ?1 and ?32766"),
    ("SELECT ?32767;", "?32767", "variable number must be between ?1 and ?32766"),
    ("SELECT ?99999999999999999999;", "?99999999999999999999", "variable number must be between ?1 and ?32766"),
    ("SELECT ?32766, ?;", "?", "too many SQL variables"),
    ("SELECT ?32766, :a;", ":a", "too many SQL variables"),
    ("SELECT #1;", "#1", 'near "#1": syntax error'),
])
def test_sqlite_refuses_numbers_and_forms_at_the_token(
        parse_sql: Callable[..., Translation], sql: str, token: str, message: str) -> None:
    """A number out of range, a statement with too many numbers and `#` with a digit are input
    errors with SQLite's message, at the first token that SQLite refuses."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == "INPUT_ERROR" and message in str(raised.value)
    assert sql.encode()[raised.value.start:raised.value.end].decode() == token


def test_the_largest_number_is_accepted(parse_sql: Callable[..., Translation]) -> None:
    """`?32766` is the largest number of the profile's limit."""
    assert numbers(parse_sql("SELECT ?32766;")) == [[parameter(32766)]]


def test_a_prefix_alone_is_a_grammar_error(parse_sql: Callable[..., Translation]) -> None:
    """`:` alone is no token of SQLite, so the grammar rejects it."""
    with pytest.raises(SqlError) as raised:
        parse_sql("SELECT :;").statements()
    assert raised.value.status == "INPUT_ERROR"
