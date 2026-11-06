"""Resolve only selected runtime prerequisites during setup, never during discovery.

The one exception is the mutant base: after collection, a session that selected a mutant
measurement builds the unchanged model once, before its first test."""

from __future__ import annotations

from collections.abc import Callable
import os
from pathlib import Path
import shutil
import subprocess
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


MUTANT_BASE = "requires_mutant_base"
"""The marker of a mutant measurement, which classifies cases with mutant copies of one built base."""


def selected_runtime_root(config: pytest.Config) -> Path:
    """The runtime root that `--runtime-root` selects, or the repository root without the option."""
    return config.getoption("runtime_root") or config.rootpath


@pytest.fixture(scope="session")
def runtime_root(pytestconfig: pytest.Config) -> Path:
    """Resolve the selected artifact root lazily, without checking unrelated prerequisites."""
    root = selected_runtime_root(pytestconfig)
    if not root.is_dir():
        pytest.fail(f"Runtime directory is missing: {root}; build the selected runtime first")
    return root.resolve()


def needs_mutant_base(items: list[pytest.Item]) -> bool:
    """Whether one of the selected tests is a mutant measurement."""
    return any(item.get_closest_marker(MUTANT_BASE) is not None for item in items)


def pytest_collection_finish(session: pytest.Session) -> None:
    """Build the unchanged model of the mutant measurements before the first test starts (#346).

    `conformance.mutant_builds.built_base` builds the base once for the process. A test that
    triggers the build would pay for it inside its own pytest-timeout limit, and so would a
    session fixture, whose setup counts against the first test that requests it. Here the build
    has only its own Lake limit and the limit of the suite. A failed build stops the session."""
    root = selected_runtime_root(session.config)
    if session.config.option.collectonly or not needs_mutant_base(session.items) or not root.is_dir():
        return  # Without the runtime root, the `runtime_root` fixture reports it in each test.
    from conformance.mutant_builds import built_base
    try:
        built_base(Path(__file__).resolve().parents[1], root.resolve() / "lean")
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        pytest.exit(f"The unchanged model of the mutant tests did not build: {error}\n"
                    "Fix the build error in packages/ and run the mutant tests again.",
                    returncode=pytest.ExitCode.TESTS_FAILED)


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
    def translate_with_selected_grammar(sql: str, version: str = "3.51.0", name_tokens: bool = False) -> Translation:
        """Translate with the grammar of the release's supported profile. The name tokens of the
        text of result columns (`Syntax.SourceText`) are removed from the answer unless `name_tokens`
        is true, so that the tests of other syntax need not repeat them; `tests/syntax_name_tokens_test.py`
        checks them."""
        from conformance.sql_text import Translation as TranslationAnswer
        translation = profile_parser(runtime_root, version).translate(sql.encode(), "fixture.sql")
        if name_tokens:
            return translation
        stripped = without_name_tokens(translation.answer)
        assert isinstance(stripped, dict)
        return TranslationAnswer(stripped)
    return translate_with_selected_grammar


def without_name_tokens(value: object) -> object:
    """The JSON with each source text object, a text with its name tokens, replaced by the plain text,
    which is the form of a text without tokens."""
    if isinstance(value, list):
        return [without_name_tokens(item) for item in value]
    if isinstance(value, dict):
        if set(value) == {"text", "tokens"} and isinstance(value["text"], str):
            return value["text"]
        return {key: without_name_tokens(item) for key, item in value.items()}
    return value
