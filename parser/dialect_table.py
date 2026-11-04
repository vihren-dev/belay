"""The dialect table: which releases the parser library has, and their grammar identities.

Each release names its two archives on sqlite.org by their SHA-256. A dialect is a release
with the grammar options in effect. Its grammar identity is a digest of its parser identity,
its tokenizer identity and its options (ADR 0029, D3): each of these is a digest of the
generated C that is compiled, so two releases share a parser, a tokenizer or a whole grammar
exactly when the compiled code is the same. `parser/dialects.json` records each dialect with
its identity, and the generation fails when the sources give another identity.
"""

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path

from parser.grammar_sources import ReleaseSources

TABLE_FIELDS = frozenset({"releases", "dialects"})
"""The fields of the dialect table object."""
RELEASE_FIELDS = frozenset({"version", "year", "sourceArchive", "amalgamationArchive"})
"""The fields of a release entry: its version, the year folder of its archives on sqlite.org,
and the SHA-256 of `sqlite-src-NNNNNNN.zip` and of `sqlite-autoconf-NNNNNNN.tar.gz`."""
DIALECT_FIELDS = frozenset({"version", "grammarOptions", "grammar"})
"""The fields of a dialect entry: its release, the grammar options in effect and its identity."""
IDENTITY_FORMAT = "sqlite-verifier-grammar-2"
"""Names the digest layout below; a new layout must change it, so no old identity matches."""
PARSER_FILES = ("syntax.c", "syntax.h", "token_map.inc")
"""The generated files of a parser that its identity digests."""


@dataclass(frozen=True)
class Release:
    """A release that the library has, and the SHA-256 of its two archives on sqlite.org."""

    version: str
    year: str
    source_archive: str
    amalgamation_archive: str


@dataclass(frozen=True)
class Dialect:
    """A built dialect and the grammar identity that the dialect table records for it."""

    version: str
    grammar_options: tuple[str, ...]
    grammar: str


@dataclass(frozen=True)
class DialectTable:
    """The checked-in dialect table: the releases to read and the dialects to build."""

    releases: tuple[Release, ...]
    dialects: tuple[Dialect, ...]


def _digest(value: dict[str, object]) -> str:
    """Return the SHA-256 of the canonical JSON text of value."""
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode()).hexdigest()


def parser_identity(files: dict[str, str]) -> str:
    """Digest the generated files of a parser that Lemon wrote with the fixed prefix `Syntax`.

    The committed files are generated again with the prefix of this identity; digesting the
    first output keeps the identity free of itself.
    """
    if set(files) != set(PARSER_FILES):
        raise ValueError(f"A parser identity digests {sorted(PARSER_FILES)}, not {sorted(files)}")
    return _digest({"parser": files})


def tokenizer_identity(cut: str) -> str:
    """Digest a tokenizer cut of `parser/tokenizer_cut.py`, which holds its token numbers."""
    return hashlib.sha256(cut.encode()).hexdigest()


def grammar_identity(parser: str, tokenizer: str, options: tuple[str, ...]) -> str:
    """Digest the format, the parser and tokenizer identities and the options in effect."""
    return _digest({"format": IDENTITY_FORMAT, "parser": parser, "tokenizer": tokenizer,
                    "grammarOptions": sorted(options)})


def _strings(value: object, where: str) -> tuple[str, ...]:
    """Return a list of strings from the table, or fail with its location."""
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{where} must be a list of strings in parser/dialects.json")
    return tuple(value)


def _text(entry: dict[str, object], key: str, where: str) -> str:
    """Return a non-empty string field of a table entry, or fail with its location."""
    value = entry.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{where} needs a non-empty string {key!r} in parser/dialects.json")
    return value


def _entries(table: dict[str, object], key: str, fields: frozenset[str]) -> list[dict[str, object]]:
    """Return the entries of one table list, each with exactly the given fields."""
    entries = table.get(key)
    if not isinstance(entries, list) or not entries or not all(
            isinstance(entry, dict) and set(entry) == fields for entry in entries):
        raise ValueError(f"{key!r} in parser/dialects.json must be a non-empty list of objects "
                         f"with the fields {sorted(fields)}")
    return entries


def load_table(path: Path) -> DialectTable:
    """Read and validate the dialect table at path."""
    table = json.loads(path.read_text())
    if not isinstance(table, dict) or set(table) != TABLE_FIELDS:
        raise ValueError(f"{path} must be an object with 'releases' and 'dialects'")
    releases = tuple(Release(*(_text(entry, key, "A release")
                               for key in ("version", "year", "sourceArchive", "amalgamationArchive")))
                     for entry in _entries(table, "releases", RELEASE_FIELDS))
    dialects = tuple(Dialect(_text(entry, "version", "A dialect"),
                             _strings(entry["grammarOptions"], "grammarOptions"),
                             _text(entry, "grammar", "A dialect"))
                     for entry in _entries(table, "dialects", DIALECT_FIELDS))
    if len({release.version for release in releases}) != len(releases):
        raise ValueError(f"{path} names a release twice")
    if len({(dialect.version, frozenset(dialect.grammar_options)) for dialect in dialects}) != len(dialects):
        raise ValueError(f"{path} names a dialect twice")
    return DialectTable(releases, dialects)


def check_release(release: Release, sources: ReleaseSources) -> None:
    """Fail when the table's version label differs from the version in the release's sqlite3.h."""
    if release.version != sources.version:
        raise ValueError(f"The archives of release {release.version} contain SQLite {sources.version}. "
                         "Correct the release entry in parser/dialects.json.")


def check_dialect(dialect: Dialect, release: ReleaseSources, identity: str) -> None:
    """Fail unless the dialect's options are grammar options of its release, the build can
    make the dialect, and the sources give the identity that the table records."""
    unknown = sorted(set(dialect.grammar_options) - set(release.grammar_options))
    if unknown:
        raise ValueError(f"Dialect {dialect.version} names options that are not grammar options "
                         f"of the release: {unknown}")
    if dialect.grammar_options:
        raise ValueError(f"Dialect {dialect.version} {list(dialect.grammar_options)} has grammar "
                         "options; the build makes only default dialects")
    if identity != dialect.grammar:
        raise ValueError(f"The sources of dialect {dialect.version} {list(dialect.grammar_options)} "
                         f"give grammar identity {identity}, but parser/dialects.json records "
                         f"{dialect.grammar}. Check the source change, then record the new identity.")
