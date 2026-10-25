"""Kernel consumers of stored-view expansion and DDL through the SQL surface."""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.parametrize("fixture", ["ClaimsViews", "ClaimsViewScope", "ClaimsViewTriggers",
    pytest.param("ClaimsViewDrop", marks=pytest.mark.requires_native("sqlite3")),
    pytest.param("ClaimsViewCreate", marks=pytest.mark.requires_native("sqlite3"))])
def test_stored_views_use_the_indexed_query_resolver(runtime_root: Path, tmp_path: Path, fixture: str) -> None:
    """QuerySourceExpansion preserves late lookup, metadata, closed names and trigger-cell
    offsets through kernel claims. Sampling checks view storage and kernel validity;
    CREATE/DROP VIEW check late binding, rollback and errors against pinned native SQLite."""
    setup_path = module_setup(runtime_root, tmp_path)
    setup = json.loads(setup_path.read_text())
    for name in ("ViewsSupport", fixture):
        setup["name"] = name
        setup_path.write_text(json.dumps(setup))
        artifact = tmp_path / f"{name}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup_path}",
                              "-o", str(artifact), str(FIXTURES / f"{name}.lean")],
                             cwd=tmp_path, timeout=90)
        assert result.returncode == 0, result.diagnostic()
        assert all(term not in result.stdout for term in ("sorryAx", "ofReduceBool", "_native")), result.stdout
        setup["importArts"][name] = [[str(artifact)]]
    if fixture == "ClaimsViewDrop":
        assert result.stdout.count("depends on axioms") == 9, result.stdout
        check_drop_messages(result.stdout, tmp_path)
    if fixture == "ClaimsViewCreate":
        assert result.stdout.count("depends on axioms") == 11, result.stdout
        check_create_messages(result.stdout, tmp_path)


def check_drop_messages(output: str, directory: Path) -> None:
    """Compare the model resolver's DROP messages with pinned SQLite, including
    wrong-kind precedence, declared spelling and unresolved view definitions."""
    statements = ["DROP VIEW mixedt", "DROP VIEW IF EXISTS mixedt", "DROP TABLE mixedv",
                  "DROP TABLE IF EXISTS mixedv", "DROP VIEW MiSsInG", "DROP VIEW idx",
                  "DROP VIEW IF EXISTS sqlite_schema", "DROP VIEW IF EXISTS missing",
                  "DROP VIEW IF EXISTS idx", "DROP VIEW broken", "DROP VIEW cycle"]
    prelude = ("CREATE TABLE MixedT(x INTEGER); INSERT INTO MixedT VALUES(7),(8);"
               "CREATE INDEX idx ON MixedT(x); CREATE VIEW MixedV AS SELECT x FROM MixedT;"
               "CREATE VIEW broken AS SELECT * FROM missing; CREATE VIEW cycle AS SELECT * FROM cycle;"
               "CREATE VIEW nested AS SELECT x FROM MixedV;")
    check_messages(output, "drop-messages:", statements, prelude, directory)


def check_create_messages(output: str, directory: Path) -> None:
    """Compare CREATE resolution with SQLite, including parameter precedence and
    the deliberate deferral of query-name and output-width checks until use."""
    statements = ["CREATE VIEW mixedt AS SELECT 1", "CREATE VIEW mixedv AS SELECT 1",
                  "CREATE VIEW IF NOT EXISTS idx AS SELECT 1", "CREATE VIEW sqlite_x AS SELECT 1",
                  "CREATE VIEW sqlite_x AS SELECT ?", "CREATE VIEW IF NOT EXISTS mixedt AS SELECT ?",
                  "CREATE VIEW IF NOT EXISTS mixedv AS WITH unused AS (SELECT ?) SELECT 1",
                  "CREATE VIEW fresh AS SELECT (SELECT ?)", "CREATE VIEW fresh AS SELECT * FROM missing",
                  "CREATE VIEW fresh AS SELECT * FROM fresh", "CREATE VIEW tr AS SELECT 1",
                  "CREATE VIEW IF NOT EXISTS mixedt AS SELECT * FROM missing", "CREATE VIEW fresh(a,b) AS SELECT 1"]
    prelude = ("CREATE TABLE MixedT(x INTEGER); INSERT INTO MixedT VALUES(7),(8);"
               "CREATE INDEX idx ON MixedT(x); CREATE VIEW MixedV AS SELECT x FROM MixedT;"
               "CREATE TRIGGER tr AFTER INSERT ON MixedT BEGIN SELECT 1; END;")
    check_messages(output, "create-messages:", statements, prelude, directory)


def check_messages(output: str, prefix: str, statements: list[str], prelude: str, directory: Path) -> None:
    """Replay each fixture's emitted model message on a fresh pinned native database."""
    messages = json.loads(next(line[len(prefix):] for line in output.splitlines() if line.startswith(prefix)))
    assert isinstance(messages, list) and len(messages) == len(statements)
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=directory, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    for statement, message in zip(statements, messages, strict=True):
        result = run_command([sqlite, "-batch", ":memory:", prelude + statement], cwd=directory, timeout=5)
        if message is None:
            assert result.returncode == 0 and not result.stderr, result.diagnostic()
        else:
            assert isinstance(message, str)
            assert result.returncode != 0, result.diagnostic()
            assert result.stderr.splitlines()[0] == "Error: in prepare, " + message, result.diagnostic()
