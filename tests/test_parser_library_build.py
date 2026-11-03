"""The parser library build reads grammar options, computes identities and checks the dialect table.

These tests check `parser/grammar_sources.py`, `parser/dialect_table.py` and
`parser/library_metadata.py` with small synthetic release folders. The generation runs the
same code on the releases' archives.
"""

import json
from pathlib import Path

import pytest

from parser.dialect_table import (PARSER_FILES, Dialect, Release, check_dialect, check_release, grammar_identity,
                                  load_table, parser_identity, tokenizer_identity)
from parser.grammar_sources import C_CONDITIONAL, LEMON_CONDITIONAL, read_release, conditional_macros
from parser.library_metadata import Grammar, ReleaseRecord, c_string, grammar_size, metadata, write_sources
from tests.parser_release_fixtures import AMALGAMATION, release

pytestmark = [pytest.mark.unit, pytest.mark.parser]
def test_conditional_macros_reads_lemon_and_c_conditionals() -> None:
    """Grammar options come from every conditional form; a test of a macro value is refused."""
    lemon = "%ifdef A\n%ifndef B\n%if C || !D\n%endif\n%else\n"
    assert conditional_macros(lemon, LEMON_CONDITIONAL) == {"A", "B", "C", "D"}
    c = "#ifdef E\n# if defined(F) && \\\n  !defined(G) /* comment H */\n#elif I\n#endif\n"
    assert conditional_macros(c, C_CONDITIONAL) == {"E", "F", "G", "I"}
    with pytest.raises(ValueError, match="macro value"):
        conditional_macros("%if X==2\n", LEMON_CONDITIONAL)


RELEASE = Release("3.51.0", "2025", "ab" * 32, "cd" * 32)
"""A release entry of the dialect table."""


def test_read_release_extracts_options_from_parser_sources_only(tmp_path: Path) -> None:
    """The tokenizer section ends at sqlite3RunParser, so its SQLITE_DEBUG test is no grammar option;
    a missing amalgamation marker fails the generation."""
    sources = read_release(release(tmp_path / "release"))
    assert (sources.version, sources.source_id) == ("3.51.0", "2025-11-04 source")
    assert sources.grammar_options == ("SQLITE_ASCII", "SQLITE_OMIT_CTE", "SQLITE_OMIT_WINDOWFUNC")
    without_tokenizer = AMALGAMATION.replace("Begin file tokenize.c", "Begin file other.c")
    with pytest.raises(ValueError, match="tokenizer"):
        read_release(release(tmp_path / "incomplete", amalgamation=without_tokenizer))


def test_identities_follow_each_compiled_input() -> None:
    """A parser identity follows each of its files, a tokenizer identity its cut, and a grammar
    identity its parser, its tokenizer and its options; a parser identity needs exactly its files."""
    files = {name: name for name in PARSER_FILES}
    parser = parser_identity(files)
    assert parser != parser_identity({**files, "syntax.c": "other"})
    assert tokenizer_identity("a") != tokenizer_identity("b")
    identities = {grammar_identity(parser, "t", ()), grammar_identity("p", "t", ()),
                  grammar_identity(parser, "u", ()), grammar_identity(parser, "t", ("SQLITE_OMIT_CTE",))}
    assert len(identities) == 4 and grammar_identity(parser, "t", ()) == grammar_identity(parser, "t", ())
    with pytest.raises(ValueError, match="digests"):
        parser_identity({"syntax.c": ""})


def test_dialect_table_checks(tmp_path: Path) -> None:
    """The generation refuses a wrong release label, unknown or unbuilt options and another identity."""
    sources = read_release(release(tmp_path / "release"))
    check_release(RELEASE, sources)
    with pytest.raises(ValueError, match="contain SQLite 3.51.0"):
        check_release(Release("3.46.0", "2024", "ab" * 32, "cd" * 32), sources)
    check_dialect(Dialect("3.51.0", (), "abc"), sources, "abc")
    with pytest.raises(ValueError, match="records abc"):
        check_dialect(Dialect("3.51.0", (), "abc"), sources, "abd")
    with pytest.raises(ValueError, match="not grammar options"):
        check_dialect(Dialect("3.51.0", ("SQLITE_THREADSAFE",), "abc"), sources, "abc")
    with pytest.raises(ValueError, match="only default dialects"):
        check_dialect(Dialect("3.51.0", ("SQLITE_OMIT_CTE",), "abc"), sources, "abc")


def test_load_table_validates_the_structure(tmp_path: Path) -> None:
    """The checked-in table loads; a duplicate dialect or a missing field is refused."""
    table = load_table(Path(__file__).resolve().parents[1] / "parser/dialects.json")
    assert table.releases[0].version == "3.51.0" and "3.46.0" in {release.version for release in table.releases}
    assert all(len(release.source_archive) == len(release.amalgamation_archive) == 64 for release in table.releases)
    assert all(not dialect.grammar_options and len(dialect.grammar) == 64 for dialect in table.dialects)
    entry = {"version": "3.51.0", "grammarOptions": [], "grammar": "abc"}
    release_entry = {"version": "3.51.0", "year": "2025", "sourceArchive": "ab", "amalgamationArchive": "cd"}
    for dialects, message in (([entry, entry], "dialect twice"), ([{"version": "3.51.0"}], "fields")):
        path = tmp_path / "dialects.json"
        path.write_text(json.dumps({"releases": [release_entry], "dialects": dialects}))
        with pytest.raises(ValueError, match=message):
            load_table(path)


def test_metadata_and_generated_c_sources(tmp_path: Path) -> None:
    """The metadata has the documented fields, and the generated C keeps its exact bytes."""
    record = ReleaseRecord("3.51.0", "2025-11-04 source", ("SQLITE_ASCII", "SQLITE_OMIT_CTE", "SQLITE_OMIT_WINDOWFUNC"))
    grammar = Grammar("ab" * 32, "Grammar_" + "ab" * 8, 409, 186)
    document = metadata([record], [Dialect("3.51.0", (), grammar.identity)], [grammar])
    assert document == {
        "api": 1,
        "releases": [{"version": "3.51.0", "sourceId": "2025-11-04 source",
                      "grammarOptions": ["SQLITE_ASCII", "SQLITE_OMIT_CTE", "SQLITE_OMIT_WINDOWFUNC"]}],
        "dialects": [{"version": "3.51.0", "grammarOptions": [], "grammar": grammar.identity}],
        "grammars": [{"grammar": grammar.identity, "productions": 409, "tokens": 186}]}
    assert c_string('a"b\\c') == '"a\\"b\\\\c"'
    write_sources(tmp_path, document, [grammar])
    assert (tmp_path / "library_grammars.inc").read_text() == f'GRAMMAR({grammar.prefix}, "{grammar.identity}")\n'
    assert grammar_size("#define YYNRULE              409\n", "#define P_SEMI 1\n#define P_ID 2\n") == (409, 2)
