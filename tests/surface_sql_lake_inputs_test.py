"""S7 Lake inputs: libraries that list their SQL files as `needs` rebuild when, and only when, the SQL text changes."""

from pathlib import Path

import pytest

from tests.sql_file_support import installed_layout, lake_build, run_checker, write_lean_package

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

INPUTS = '''input_dir sqlFiles where
  path := "sql"
  text := true
  filter := .extension "sql"

input_file oneFile where
  path := "one.sql"
  text := true
'''
"""The inputs that the documented lakefile declares: a folder of `.sql` files, and one file."""

FOLDER_USER = 'import Belay\n\n/-- Reads a file of the folder input. -/\ndef first := sql_file "sql/a.sql"\n'
"""A module of the library that needs the folder."""
FILE_USER = 'import Belay\n\n/-- Reads the file input. -/\ndef only := sql_file "one.sql"\n'
"""A module of the library that needs the file."""


def rebuilt(installed: Path, package: Path, library: str) -> bool:
    """Run `lake build` for the library and say whether Lake compiled the library's module again."""
    result = lake_build(installed, package, library)
    assert result.returncode == 0, result.diagnostic()
    return f"Built {library}" in result.stdout


def make_package(runtime_root: Path, tmp_path: Path) -> tuple[Path, Path]:
    """A package with the libraries Folder (needs `sqlFiles`) and File (needs `oneFile`), built once."""
    installed = installed_layout(runtime_root, tmp_path)
    package = tmp_path / "inputs"
    write_lean_package(package, "Inputs", installed, [], inputs=INPUTS)
    with (package / "lakefile.lean").open("a") as lakefile:
        for library, need in {"Folder": "sqlFiles", "File": "oneFile"}.items():
            lakefile.write(f'\nlean_lib {library} where\n  srcDir := "lean"\n  roots := #[`{library}]\n  needs := #[{need}]\n')
    (package / "sql/a.sql").write_bytes(b"SELECT 1;\r\nSELECT 2;\r\n")
    (package / "one.sql").write_text("SELECT 9;\n")
    (package / "lean/Folder.lean").write_text(FOLDER_USER)
    (package / "lean/File.lean").write_text(FILE_USER)
    assert rebuilt(installed, package, "Folder") and rebuilt(installed, package, "File")
    return installed, package


def test_folder_input_rebuilds_for_sql_changes_only(runtime_root: Path, tmp_path: Path) -> None:
    """The `input_dir` and `needs` lakefile lines that the checker's report recommends (`SqlCheckReport.lean`,
    `LibraryCheck.render`): an SQL text edit or a new `.sql` file rebuilds the library and makes the checker fresh,
    while a file of another type, a line-ending-only edit and an unchanged tree do not rebuild it."""
    installed, package = make_package(runtime_root, tmp_path)
    assert not rebuilt(installed, package, "Folder")
    (package / "sql/notes.txt").write_text("not SQL\n")
    assert not rebuilt(installed, package, "Folder")
    (package / "sql/a.sql").write_bytes(b"SELECT 1;\nSELECT 2;\n")
    assert not rebuilt(installed, package, "Folder")
    result = run_checker(installed, package, "--library", "Folder")
    assert result.returncode == 0, result.diagnostic()
    (package / "sql/a.sql").write_text("SELECT 1;\nSELECT 3;\n")
    result = run_checker(installed, package, "--library", "Folder")
    assert result.returncode == 1 and "lake build Folder" in result.stdout, result.diagnostic()
    assert rebuilt(installed, package, "Folder")
    result = run_checker(installed, package, "--library", "Folder")
    assert result.returncode == 0, result.diagnostic()
    (package / "sql/added.sql").write_text("SELECT 5;\n")
    assert rebuilt(installed, package, "Folder")
    assert not rebuilt(installed, package, "File")


def test_file_input_rebuilds_for_its_own_text_only(runtime_root: Path, tmp_path: Path) -> None:
    """An `input_file` in `needs` (`SqlCheckReport.lean`, `LibraryCheck.render`) rebuilds only the library that
    lists it, and only for a change of its text, not of its line ends."""
    installed, package = make_package(runtime_root, tmp_path)
    (package / "one.sql").write_bytes(b"SELECT 9;\r\n")
    assert not rebuilt(installed, package, "File")
    (package / "one.sql").write_text("SELECT 10;\n")
    result = run_checker(installed, package, "--library", "File")
    assert result.returncode == 1 and "one.sql changed" in result.stdout, result.diagnostic()
    assert not rebuilt(installed, package, "Folder")
    assert rebuilt(installed, package, "File")
    result = run_checker(installed, package, "--library", "File")
    assert result.returncode == 0, result.diagnostic()
