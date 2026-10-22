"""The parse refusals of the text package's program, through the harness's client
(`conformance/sql_text.py`), and quoted Lean text.

These tests check how the harness classifies parser failures, independently of the statement
mapping. `tests/surface/TranslationChecks.lean` checks that the binding refuses a parse document
for another grammar.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from belay.sqlite.quoted_text import quoted_string
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


@pytest.mark.parametrize("sql,status", [("CREATE TABLE", "INPUT_ERROR"), (" " * (1024 * 1024 + 1), "UNVERIFIED")],
                         ids=["syntax", "resource_limit"])
def test_parser_failure_classes(parse_sql: Callable[..., Translation], sql: str, status: str) -> None:
    """Resource exhaustion does not become a syntax error or a violated theorem."""
    with pytest.raises(SqlError) as rejected:
        parse_sql(sql).parsed()
    assert rejected.value.status == status


def test_grammar_rejection_names_the_place_and_the_next_step(parse_sql: Callable[..., Translation]) -> None:
    """The client reports a grammar rejection with the source, the offset and what to do next."""
    with pytest.raises(SqlError) as rejected:
        parse_sql("CREATE TABLE t(a TEXT); SELEC 1;").parsed()
    assert rejected.value.status == "INPUT_ERROR"
    assert rejected.value.source == "fixture.sql" and rejected.value.start == 24
    assert "correct the SQL there and run the command again" in str(rejected.value)


def test_quoted_lean_text_escapes_controls() -> None:
    """`quoted_string` writes Lean's escapes for quotes, backslashes and control characters."""
    assert quoted_string('a\b\f"\\\n') == '"a\\u0008\\u000c\\"\\\\\\u000a"'
