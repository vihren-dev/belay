"""Generate the parser and the tokenizer of one SQLite release, with their identities.

`build-support/parser-library.nix` runs this step once for each release of
`parser/dialects.json`, in a folder with the release's `parse.y`, `lempar.c`, `sqlite3.c`
and `sqlite3.h`, the `lemon` program built from its `lemon.c`, and Lemon's outputs `parse.h`,
`preprocessed.y` (`-E`) and `grammar.y` (`-g`). The step (ADR 0029, D2 and D3):

- cuts the tokenizer out of `sqlite3.c` and runs the slice check on the cut;
- generates the parser with the fixed prefix `Syntax`, digests it, and generates it again
  with the prefix of its identity;
- checks the production count against Lemon's export, the release's version label and the
  grammar identity of each of its dialects in the table.

It writes `parser/`, `tokenizer/` and `release.json` into the output folder.
"""

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from parser.dialect_table import (PARSER_FILES, DialectTable, check_dialect, check_release, grammar_identity,
                                  load_table, parser_identity, tokenizer_identity)
from parser.generate import generate
from parser.grammar_sources import read_release
from parser.library_metadata import grammar_size
from parser.slice_check import check_slice
from parser.tokenizer_cut import cut_tokenizer, token_names, tokens_header

PREFIX_DIGITS = 16
"""The identity digits in a parser's, tokenizer's or grammar's symbol prefix and folder name;
`parser/library_steps.py` fails if two identities share them."""
LEMON_TIMEOUT_SECONDS = 120
"""The limit for one Lemon run on the rewritten grammar."""


@dataclass(frozen=True)
class ReleaseOutput:
    """What one release step found: the release, its identities and its parser's size."""

    version: str
    source_id: str
    grammar_options: tuple[str, ...]
    parser: str
    tokenizer: str
    grammar: str
    productions: int
    tokens: int


def short(identity: str) -> str:
    """Return the digits of an identity that name its folder and its symbol prefix."""
    return identity[:PREFIX_DIGITS]


def lemon_parser(sources: Path, cut: str, prefix: str) -> dict[str, str]:
    """Rewrite the release's grammar with Lemon prefix `prefix` and return the parser files.

    Lemon runs in a temporary folder with relative file names, so its `#line` directives
    name no path.
    """
    with tempfile.TemporaryDirectory() as work:
        folder = Path(work)
        generate((sources / "preprocessed.y").read_text(), (sources / "grammar.y").read_text(),
                 (sources / "parse.h").read_text(), cut, folder / "syntax.y", prefix)
        shutil.copy(sources / "lempar.c", folder / "lempar.c")
        subprocess.run([str(sources / "lemon"), "-q", "-Tlempar.c", "syntax.y"], cwd=folder, check=True,
                       timeout=LEMON_TIMEOUT_SECONDS)
        return {name: (folder / name).read_text() for name in PARSER_FILES}


def production_count(files: dict[str, str], sources: Path) -> tuple[int, int]:
    """Return the parser's production and token counts; fail unless Lemon's export agrees."""
    productions, tokens = grammar_size(files["syntax.c"], files["syntax.h"])
    exported = sum(1 for line in (sources / "grammar.y").read_text().splitlines() if "::=" in line)
    if productions != exported:
        raise ValueError(f"The generated parser has {productions} productions, but Lemon's grammar "
                         f"export has {exported}; check parser/generate.py")
    return productions, tokens


def release_step(sources: Path, table: DialectTable, version: str, compiler: str, flags: list[str],
                 parser_folder: Path, output: Path) -> ReleaseOutput:
    """Generate and check one release's parser and tokenizer; write them into output."""
    release = next((entry for entry in table.releases if entry.version == version), None)
    if release is None:
        raise ValueError(f"parser/dialects.json has no release {version}")
    read = read_release(sources)
    check_release(release, read)
    cut = cut_tokenizer((sources / "sqlite3.c").read_text())
    tokenizer_folder = output / "tokenizer"
    tokenizer_folder.mkdir(parents=True)
    for name, text in (("sqlite3_tokenizer.c", cut), ("tokens.h", tokens_header(cut)),
                       ("token_names.inc", token_names(cut))):
        (tokenizer_folder / name).write_text(text)
    check_slice(compiler, flags, parser_folder, tokenizer_folder, sources / "sqlite3.c")
    parser = parser_identity(lemon_parser(sources, cut, "Syntax"))
    files = lemon_parser(sources, cut, "Syntax_" + short(parser))
    productions, tokens = production_count(files, sources)
    (output / "parser").mkdir()
    for name, text in files.items():
        (output / "parser" / name).write_text(text)
    tokenizer = tokenizer_identity(cut)
    grammar = grammar_identity(parser, tokenizer, ())
    for dialect in (entry for entry in table.dialects if entry.version == version):
        check_dialect(dialect, read, grammar)
    record = ReleaseOutput(read.version, read.source_id, read.grammar_options, parser, tokenizer, grammar,
                           productions, tokens)
    (output / "release.json").write_text(json.dumps(asdict(record)))
    return record


def main() -> None:
    """Run the step from the command line."""
    cli = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for name in ("--sources", "--table", "--parser", "--output"):
        cli.add_argument(name, type=Path, required=True)
    cli.add_argument("--version", required=True)
    cli.add_argument("--compiler", required=True)
    cli.add_argument("--flag", action="append", default=[], help="a compile flag of the manifest")
    arguments = cli.parse_args()
    release_step(arguments.sources, load_table(arguments.table), arguments.version, arguments.compiler,
                 arguments.flag, arguments.parser, arguments.output)


if __name__ == "__main__":
    main()
