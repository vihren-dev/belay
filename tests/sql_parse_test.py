"""The parser boundary of the frontend: `belay.sqlite.sql_tree.parse` and quoted Lean text.

These tests check how the frontend reads the pinned parser library's document, and
how it classifies parser failures, independently of the statement mapping.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from belay.sqlite.errors import SqlError
from belay.sqlite.quoted_text import quoted_string
from belay.sqlite.sql_tree import SqlParser, Tree, parse
from tests.runtime_fixtures import profile_parser

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def test_result_for_another_grammar_is_rejected(runtime_root: Path) -> None:
    """`parse` refuses a library document for another grammar than the one it requested."""
    parser = profile_parser(runtime_root)

    class OtherGrammar:
        """A library whose documents name another grammar."""

        metadata = parser.library.metadata

        def parse(self, grammar: str, sql: bytes) -> object:
            """Return the real document with another grammar identity."""
            return {**parser.library.parse(grammar, sql), "grammar": "0" * 64}  # type: ignore[dict-item]

    with pytest.raises(SqlError) as rejected:
        parse(SqlParser(OtherGrammar(), parser.grammar), b'CREATE TABLE t(x TEXT);', 'fixture.sql')  # type: ignore[arg-type]
    assert rejected.value.status == 'UNVERIFIED'
    assert 'another grammar' in str(rejected.value)


@pytest.mark.parametrize("sql,status", [("CREATE TABLE", "INPUT_ERROR"), (" " * (1024 * 1024 + 1), "UNVERIFIED")],
                         ids=["syntax", "resource_limit"])
def test_parser_failure_classes(parse_sql: Callable[..., Tree], sql: str, status: str) -> None:
    """Resource exhaustion does not become a syntax error or a violated theorem."""
    with pytest.raises(SqlError) as rejected:
        parse_sql(sql)
    assert rejected.value.status == status


def test_grammar_rejection_names_the_place_and_the_next_step(parse_sql: Callable[..., Tree]) -> None:
    """`parse` reports a grammar rejection with the source, the offset and what to do next."""
    with pytest.raises(SqlError) as rejected:
        parse_sql("CREATE TABLE t(a TEXT); SELEC 1;")
    assert rejected.value.status == "INPUT_ERROR"
    assert rejected.value.source == "fixture.sql" and rejected.value.start == 24
    assert "correct the SQL there and run the command again" in str(rejected.value)


def test_quoted_lean_text_escapes_controls() -> None:
    """`quoted_string` writes Lean's escapes for quotes, backslashes and control characters."""
    assert quoted_string('a\b\f"\\\n') == '"a\\u0008\\u000c\\"\\\\\\u000a"'
