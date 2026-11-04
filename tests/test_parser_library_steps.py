"""The library step writes one folder for each parser and tokenizer identity, and the manifest.

These tests check `library_sources` of `parser/library_steps.py`, which the generation of
`build-support/parser-library.nix` runs on the outputs of the release steps, with synthetic
release outputs. The `parserLibrary` suite checks the library compiled from the real tree.
"""

from dataclasses import asdict
import json
from pathlib import Path

import pytest

from parser.dialect_table import Dialect, DialectTable, Release
from parser.library_steps import library_sources, read_release_output
from parser.release_step import ReleaseOutput

pytestmark = [pytest.mark.unit, pytest.mark.parser]


def release_output(folder: Path, version: str, parser: str, tokenizer: str, grammar: str, text: str = "c") -> Path:
    """Write the output of one release step with one-file parser and tokenizer folders."""
    for kind in ("parser", "tokenizer"):
        (folder / kind).mkdir(parents=True)
        (folder / kind / "file").write_text(text)
    record = ReleaseOutput(version, "source " + version, ("SQLITE_A",), parser, tokenizer, grammar, 409, 186)
    (folder / "release.json").write_text(json.dumps(asdict(record)))
    return folder


def table(*versions: str) -> DialectTable:
    """A dialect table with one default dialect for each version."""
    return DialectTable(tuple(Release(version, "2025", "a", "b") for version in versions),
                        tuple(Dialect(version, (), "g" + version) for version in versions))


@pytest.mark.timeout(10)
def test_releases_share_the_folders_of_equal_identities(tmp_path: Path) -> None:
    """Two releases with one parser and two tokenizers give one parser folder, two tokenizer
    folders and two grammars, each naming its parts in the manifest."""
    first = release_output(tmp_path / "first", "3.51.0", "p" * 64, "t" * 64, "g" * 64)
    second = release_output(tmp_path / "second", "3.51.1", "p" * 64, "u" * 64, "h" * 64)
    output = tmp_path / "output"
    output.mkdir()
    library_sources(table("3.51.0", "3.51.1"), [first, second], ["-O1"], output)
    manifest = json.loads((output / "manifest.json").read_text())
    assert manifest == {
        "flags": ["-O1"],
        "parsers": [{"folder": "p" * 16, "prefix": "Syntax_" + "p" * 16}],
        "tokenizers": [{"folder": "t" * 16, "prefix": "Tokenizer_" + "t" * 16},
                       {"folder": "u" * 16, "prefix": "Tokenizer_" + "u" * 16}],
        "grammars": [{"prefix": "Grammar_" + "g" * 16, "parser": "p" * 16, "tokenizer": "t" * 16},
                     {"prefix": "Grammar_" + "h" * 16, "parser": "p" * 16, "tokenizer": "u" * 16}]}
    assert sorted(path.name for path in (output / "tokenizers").iterdir()) == ["t" * 16, "u" * 16]
    assert read_release_output(second).grammar_options == ("SQLITE_A",)


@pytest.mark.timeout(10)
def test_the_step_refuses_conflicts_and_another_order(tmp_path: Path) -> None:
    """One identity with other bytes, two identities with one folder name, or releases in
    another order than the table's fail the step."""
    first = release_output(tmp_path / "first", "3.51.0", "p" * 64, "t" * 64, "g" * 64)
    changed = release_output(tmp_path / "changed", "3.51.1", "p" * 64, "u" * 64, "h" * 64, text="other")
    clash = release_output(tmp_path / "clash", "3.51.1", "p" * 16 + "q" * 48, "u" * 64, "h" * 64)
    for folders, versions, message in (([first, changed], ("3.51.0", "3.51.1"), "different files"),
                                       ([first, clash], ("3.51.0", "3.51.1"), "same folder name"),
                                       ([first], ("3.51.1",), "table's order")):
        output = tmp_path / ("output-" + message.replace(" ", "-").replace("'", ""))
        output.mkdir()
        with pytest.raises(ValueError, match=message):
            library_sources(table(*versions), folders, [], output)
