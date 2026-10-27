"""The translation records the name tokens of the text of a result column in the body of a stored view
(`packages/belay-sqlite-text/Belay/Sqlite/Translation/NameTokens.lean`, through the text package's program).

SQLite names an unaliased view column by the text of its expression, and a rename rewrites the name tokens of
that text. These tests check the JSON that Lean's `Syntax.SourceText` decoder reads: where each name stands
in the text, how it was quoted, its node paths, and the subquery that holds it. A text without a name, and the
text of a result column outside a view, stay plain strings. `tests/surface/NameTokenPaths.lean` checks that the
paths are those of the name trace.
"""

from collections.abc import Callable, Iterator

import pytest

from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def written(source: object) -> list[tuple[str, str, int | None]]:
    """Each token of a source text as the bytes it covers, its quote and its subquery."""
    assert isinstance(source, dict)
    encoded = source["text"].encode()
    return [(encoded[item["start"]:item["stop"]].decode(), item["quote"], item["subquery"]) for item in source["tokens"]]


def paths_of(source: object, name: str) -> list[list[int]]:
    """The paths of the first token that covers the name in the source text."""
    assert isinstance(source, dict)
    encoded = source["text"].encode()
    [item] = [item for item in source["tokens"] if encoded[item["start"]:item["stop"]].decode() == name][:1]
    return item["paths"]


def view_of(parse_sql: Callable[..., Translation], query: str) -> dict[str, object]:
    """The fields of `CREATE VIEW v AS query`, with the name tokens kept."""
    [statement] = [item.value for item in parse_sql(f"CREATE VIEW v AS {query}", name_tokens=True).statements()]
    assert isinstance(statement, dict)
    return statement["createView"]


def column_texts(parse_sql: Callable[..., Translation], query: str) -> list[object]:
    """The `text` of each result column of the query of a view, in column order."""
    return [column["expression"]["text"] for column in view_of(parse_sql, query)["query"]["columns"] if column != "star"]


def source_texts(value: object) -> Iterator[dict[str, object]]:
    """Each object in the JSON that holds a text with its name tokens."""
    if isinstance(value, list):
        for item in value:
            yield from source_texts(item)
    elif isinstance(value, dict):
        if set(value) == {"text", "tokens"}:
            yield value
        for item in value.values():
            yield from source_texts(item)


def test_names_of_an_expression_have_offsets_paths_and_quotes(parse_sql: Callable[..., Translation]) -> None:
    """Each name of the text stands at its offsets with its quote and the node path that the trace
    uses: the left operand of `+` is step 1 (step 0 is the operator), the left operand of `||` is step 0, the
    quoted name keeps its quotes in the range, and the two names of `t.c` are the parts 0 and 1 of the
    qualified name."""
    first, second, third = column_texts(parse_sql, 'SELECT a + 1, "b" || t.c, [x y] + `z` FROM t;')
    assert written(first) == [("a", "none", None)]
    assert written(second) == [('"b"', "double", None), ("t", "none", None), ("c", "none", None)]
    assert written(third) == [("[x y]", "bracket", None), ("`z`", "backtick", None)]
    assert [1] in paths_of(first, "a")
    assert [0] in paths_of(second, '"b"') and paths_of(second, "t") == [[1, 0]] and paths_of(second, "c") == [[1, 1]]
    assert [1] in paths_of(third, "[x y]") and [2] in paths_of(third, "`z`")


def test_a_result_column_outside_a_view_has_no_tokens(parse_sql: Callable[..., Translation]) -> None:
    """The text of a result column of a SELECT, an INSERT query or RETURNING is a plain string, as the
    model does not rewrite it."""
    statements = [item.value for item in parse_sql(
        "SELECT a + 1 FROM t; INSERT INTO w SELECT x + y FROM s RETURNING x + 1;", name_tokens=True).statements()]
    assert list(source_texts(statements)) == []


def test_a_single_quoted_name_where_the_grammar_expects_a_name_is_a_token(parse_sql: Callable[..., Translation]) -> None:
    """SQLite reads `t.'a'` as the column `a` of `t`, so its text has the token `'a'` of the kind
    `single`, while the string literal of `'a' || b` is no name token."""
    qualified, literal = column_texts(parse_sql, "SELECT t.'a' + 1, 'a' || b FROM t;")
    assert written(qualified) == [("t", "none", None), ("'a'", "single", None)]
    assert written(literal) == [("b", "none", None)]


def test_a_text_without_a_name_is_a_plain_string(parse_sql: Callable[..., Translation]) -> None:
    """A literal has no name token, so its text keeps the plain form that it had before the tokens."""
    assert column_texts(parse_sql, "SELECT 1, 'a b', 2.5 + 1 FROM t;") == ["1", "'a b'", "2.5 + 1"]


def test_names_of_a_subquery_in_the_text_name_the_subquery(parse_sql: Callable[..., Translation]) -> None:
    """The names inside `(select ... )` are tokens of the outer text with the index of the subquery in
    the statement's list; their paths run from the subquery. Alias `t2` and table `t` are names too, and a
    second subquery has the next index."""
    [text] = column_texts(parse_sql, "SELECT (select a from t t2 where t2.a > 0) FROM t;")
    assert written(text) == [("a", "none", 0), ("t", "none", 0), ("t2", "none", 0), ("t2", "none", 0), ("a", "none", 0)]
    assert [0, 0, 0] in paths_of(text, "a") and paths_of(text, "t2") == [[1, 1]]
    [outer] = column_texts(parse_sql, "SELECT a IN (SELECT a FROM u WHERE d > (SELECT b FROM t)) FROM t;")
    assert [name for name in written(outer) if name[0] in ("a", "b", "u", "d", "t")] == [
        ("a", "none", None), ("a", "none", 0), ("u", "none", 0), ("d", "none", 0), ("b", "none", 1), ("t", "none", 1)]


def test_columns_of_with_definitions_and_derived_tables_have_tokens(parse_sql: Callable[..., Translation]) -> None:
    """A column of an indexed subquery, a WITH definition or a derived table, which a view can show as the
    name of its column, records its own tokens, with paths from its expression."""
    definition, derived = view_of(
        parse_sql, "WITH c AS (SELECT a+1 FROM t) SELECT * FROM c, (SELECT [x y] FROM t) AS d;")["subqueries"]
    assert written(definition["columns"][0]["expression"]["text"]) == [("a", "none", None)]
    assert written(derived["columns"][0]["expression"]["text"]) == [("[x y]", "bracket", None)]
    assert [] in paths_of(derived["columns"][0]["expression"]["text"], "[x y]")


def test_every_token_is_a_name_of_its_text(parse_sql: Callable[..., Translation]) -> None:
    """In views, the bytes of each token begin like a name (a letter, a quote or an underscore), and the
    offsets are in order and inside the text."""
    statements = [
        "CREATE VIEW v AS SELECT a+1, \"B\" * t.c, (SELECT max(d) FROM u WHERE u.a = t.a) FROM t;",
        "CREATE VIEW v AS SELECT x + y, [q] FROM s UNION SELECT 1, 2 FROM s;",
        "CREATE VIEW v AS SELECT `é` + 1, café, a IN (SELECT b FROM u) FROM t;",
        "CREATE VIEW v(p, q) AS WITH c AS (SELECT a + b FROM t) SELECT * FROM c;"]
    checked = 0
    for sql in statements:
        for source in source_texts([item.value for item in parse_sql(sql, name_tokens=True).statements()]):
            text = source["text"]
            assert isinstance(text, str) and isinstance(source["tokens"], list)
            encoded = text.encode()
            previous = 0
            for item in source["tokens"]:
                assert previous <= item["start"] < item["stop"] <= len(encoded)
                covered = encoded[item["start"]:item["stop"]].decode()
                assert covered[0].isalpha() or covered[0] in "\"[`'_"
                previous = item["stop"]
                checked += 1
    assert checked >= 20
