"""The name tokens of result columns against the name trace (`tests/surface/NameTokenPaths.lean`)."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_name_tokens_stand_where_the_trace_puts_the_names(runtime_root: Path, tmp_path: Path) -> None:
    """For view bodies with qualified, quoted and nested names, each name token of a result column
    (`Syntax.NameToken`) has a path whose range in the statement is the token's bytes in the text of the
    column, and each exact occurrence of the name trace of the same query as a SELECT inside a result column has a
    token with the path of the occurrence, also in a subquery of the column. This checks that a client can match the tokens of
    a stored text to the occurrences that the model's resolver reports."""
    result = run_command(surface_command(runtime_root, FIXTURES / "NameTokenPaths.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()
