"""Resolve only selected runtime prerequisites during setup, never during discovery."""

from __future__ import annotations

from collections.abc import Callable
import os
from pathlib import Path
import shutil
from typing import TYPE_CHECKING

import pytest

from tests.runtime_support import run_command

if TYPE_CHECKING:
    from conformance.sql_text import TextParser, Translation

TRANSLATION_PROGRAM = "translation-program"
"""The `requires_native` requirement of the runtime's translation program, which links the SQLite
parser library."""
TRANSLATION_PROGRAM_PATH = ".lake/build/bin/belay-sqlite-translate"
"""The program in a runtime root. Nix test targets that do not declare the harness sources load
this plugin too, so it cannot import `conformance.sql_text.PROGRAM`; the program's test checks
that both are the same path."""


def require_file(path: Path, *, executable: bool = False) -> Path:
    """Fail setup with the missing build artifact rather than silently dropping coverage."""
    if not path.is_file() or (executable and not os.access(path, os.X_OK)):
        pytest.fail(f"Required runtime file is missing or unusable: {path}; build the runtime first")
    return path


@pytest.fixture(scope="session")
def lean_sysroot(runtime_root: Path) -> Path:
    """Use the selected runtime's toolchain or resolve the pinned source compiler explicitly."""
    bundled = runtime_root / "lean"
    if (bundled / "bin/lean").is_file():
        require_file(bundled / "bin/lean", executable=True)
        return bundled.resolve()
    compiler = shutil.which("lean")
    if compiler is None:
        pytest.fail("Required Lean compiler is missing; enter the pinned shell and run just setup")
    result = run_command([compiler, "--print-prefix"], cwd=runtime_root, timeout=10)
    if result.returncode:
        pytest.fail(f"Cannot resolve Lean toolchain: {result.diagnostic()}")
    root = Path(result.stdout.strip())
    require_file(root / "bin/lean", executable=True)
    return root.resolve()


@pytest.fixture(scope="session")
def lean_libraries(runtime_root: Path) -> tuple[Path, Path]:
    """Require the runtime's own library folder and the model's, in import precedence order. The
    runtime's folder holds the conformance runner's modules in the conformance runtime."""
    application = runtime_root / ".lake/build/lib/lean"
    model = runtime_root / "packages/belay-sqlite-model/.lake/build/lib/lean"
    if not application.is_dir():
        pytest.fail(f"Required runtime library folder is missing: {application}; build the runtime first")
    require_file(model / "Belay/Sqlite/Model.olean")
    return application, model


@pytest.fixture(autouse=True)
def selected_prerequisites(request: pytest.FixtureRequest) -> None:
    """Resource markers drive setup errors; pure cases do not request any runtime fixture."""
    lean = request.node.get_closest_marker("requires_lean")
    if lean is not None:
        request.getfixturevalue("lean_sysroot")
        if lean.args != ("compiler",):
            request.getfixturevalue("lean_libraries")
    native = request.node.get_closest_marker("requires_native")
    if native is not None:
        for tool in native.args or (TRANSLATION_PROGRAM,):
            if tool == TRANSLATION_PROGRAM:
                require_file(request.getfixturevalue("runtime_root") / TRANSLATION_PROGRAM_PATH, executable=True)
            elif not isinstance(tool, str) or shutil.which(tool) is None:
                pytest.fail(f"Required native tool is missing: {tool}")
    if request.node.get_closest_marker("requires_nix") is not None and shutil.which("nix") is None:
        pytest.fail("Required Nix command is missing; enter the pinned shell")


def profile_parser(runtime_root: Path, version: str = "3.51.0") -> TextParser:
    """Return the runtime's translation program for the supported profile of a SQLite release.

    The implementation imports stay inside the function: Nix test targets that do not
    declare the Python sources still load this plugin.
    """
    from belay.sqlite.profiles import profile
    from conformance.sql_text import ProfileIdentity, TextParser, runtime_translator

    selected = profile(version)
    return TextParser.for_profile(runtime_translator(runtime_root), ProfileIdentity(selected.engine, selected.source_id))


@pytest.fixture
def parse_sql(runtime_root: Path) -> Callable[..., Translation]:
    """Translate SQL with the runtime's translation program, with the grammar of the requested
    SQLite release (`packages/belay-sqlite-text`)."""
    def translate_with_selected_grammar(sql: str, version: str = "3.51.0") -> Translation:
        """Translate with the grammar of the release's supported profile."""
        return profile_parser(runtime_root, version).translate(sql.encode(), "fixture.sql")
    return translate_with_selected_grammar
