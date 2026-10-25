"""S7 freshness checker with a package-root override: records keep pointing at the file that the form read."""

from pathlib import Path

import pytest

from tests.sql_file_support import installed_layout, lake_build, run_checker, write_same_name_projects

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_same_name_projects_are_checked_against_the_file_each_form_read(runtime_root: Path, tmp_path: Path) -> None:
    """`sourceFile` and `checkSource` (`BelaySqlCheck.lean`) with `SqlRootOverride` records of `belay.sql.packageRoot` forms: two projects of one
    package name, each with its own `sql/query.sql`, are fresh after a build, and an edit of either file is stale
    without any rebuild, so the override gives neither a false stale nor an unconditional fresh result."""
    installed = installed_layout(runtime_root, tmp_path)
    write_same_name_projects(tmp_path, installed, with_option=True)
    consumer = tmp_path / "consumer"
    result = lake_build(installed, consumer, "Consumer")
    assert result.returncode == 0, result.diagnostic()
    result = run_checker(installed, consumer)
    assert result.returncode == 0 and "2 SQL sources, 0 stale" in result.stdout, result.diagnostic()
    for file, shown in ((tmp_path / "dependency/sql/query.sql", "sql/query.sql"),
                        (tmp_path / "dependency/lean/sql/query.sql", "lean/sql/query.sql")):
        original = file.read_text()
        file.write_text(original + " -- edited")
        result = run_checker(installed, consumer)
        assert result.returncode == 1 and "1 stale" in result.stdout, result.diagnostic()
        assert f"  Twin: {shown} changed" in result.stdout, result.diagnostic()
        file.write_text(original)
