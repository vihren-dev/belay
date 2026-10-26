"""The paths of the model's name trace against the translated SQL (`tests/surface/NameTraceSpans.lean`)."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_name_trace_paths_select_the_names(runtime_root: Path, tmp_path: Path) -> None:
    """For the queries and writes of the fixture, each exact occurrence of the name trace
    (`resolveStatementTraced`) has a path that `Span.select` maps to the token of its name, and the
    number of names checked for each statement is the one that the fixture expects. This checks that the
    paths of the model locate names in the text of the translator."""
    result = run_command(surface_command(runtime_root, FIXTURES / "NameTraceSpans.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()
