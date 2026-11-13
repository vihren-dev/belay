"""The steps of the parser library build after the release steps, one command for each.

`build-support/parser-library.nix` runs `parser/release_step.py` for each release, then:

- `sources`: write the tree that is committed as `parser/generated` (ADR 0029, D3): one
  folder for each parser identity and one for each tokenizer identity, the grammar list and
  the metadata document that `library.c` includes, and the manifest that the Lake build and
  the Nix library read;
- `exports`: fail unless the linked library exports exactly the public API.
"""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from parser.dialect_table import DialectTable, load_table
from parser.library_metadata import Grammar, ReleaseRecord, metadata, write_sources
from parser.release_step import ReleaseOutput, short

PUBLIC_API = frozenset({"belay_sqlite_parser_metadata", "belay_sqlite_parser_parse",
                        "belay_sqlite_parser_free"})
"""The only symbols that the library exports; see `parser/library.h`."""
NM_TIMEOUT_SECONDS = 60
"""The limit for listing the symbols of the linked library."""


def read_release_output(folder: Path) -> ReleaseOutput:
    """Read the record that a release step wrote into folder."""
    value = json.loads((folder / "release.json").read_text())
    return ReleaseOutput(**{**value, "grammar_options": tuple(value["grammar_options"])})


def _copy_identity(source: Path, target: Path, identity: str) -> None:
    """Copy one parser or tokenizer folder; fail if the identity's folder has other bytes."""
    if target.exists():
        if any((target / path.name).read_bytes() != path.read_bytes() for path in source.iterdir()):
            raise ValueError(f"Two releases give identity {identity} with different files")
        return
    shutil.copytree(source, target)


def library_sources(table: DialectTable, folders: list[Path], flags: list[str], output: Path) -> None:
    """Write the committed tree for the release outputs in folders, in the table's order."""
    outputs = [read_release_output(folder) for folder in folders]
    if [record.version for record in outputs] != [release.version for release in table.releases]:
        raise ValueError(f"The library step got releases {[r.version for r in outputs]}, but "
                         f"parser/dialects.json lists {[r.version for r in table.releases]}; "
                         "build-support/parser-library.nix must pass them in the table's order")
    grammars: dict[str, Grammar] = {}
    pairs: dict[str, tuple[str, str]] = {}
    for folder, record in zip(folders, outputs):
        _copy_identity(folder / "parser", output / "parsers" / short(record.parser), record.parser)
        _copy_identity(folder / "tokenizer", output / "tokenizers" / short(record.tokenizer), record.tokenizer)
        grammars[record.grammar] = Grammar(record.grammar, "Grammar_" + short(record.grammar),
                                           record.productions, record.tokens)
        pairs[record.grammar] = (short(record.parser), short(record.tokenizer))
    for kind in ("parsers", "tokenizers"):
        identities = {getattr(record, kind[:-1]) for record in outputs}
        if len({short(identity) for identity in identities}) != len(identities):
            raise ValueError(f"Two {kind} have the same folder name; increase PREFIX_DIGITS "
                             "in parser/release_step.py")
    if len({grammar.prefix for grammar in grammars.values()}) != len(grammars):
        raise ValueError("Two grammars have the same symbol prefix; increase PREFIX_DIGITS in parser/release_step.py")
    releases = [ReleaseRecord(record.version, record.source_id, record.grammar_options) for record in outputs]
    write_sources(output, metadata(releases, list(table.dialects), list(grammars.values())), list(grammars.values()))
    manifest = {
        "flags": flags,
        "parsers": [{"folder": short(identity), "prefix": "Syntax_" + short(identity)}
                    for identity in dict.fromkeys(record.parser for record in outputs)],
        "tokenizers": [{"folder": short(identity), "prefix": "Tokenizer_" + short(identity)}
                       for identity in dict.fromkeys(record.tokenizer for record in outputs)],
        "grammars": [{"prefix": grammar.prefix, "parser": pairs[identity][0], "tokenizer": pairs[identity][1]}
                     for identity, grammar in grammars.items()],
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


def exported_symbols(library: Path, darwin: bool) -> set[str]:
    """Return the names of the symbols that the shared library defines and exports."""
    command = ["nm", "-gU", str(library)] if darwin else ["nm", "-D", "--defined-only", str(library)]
    output = subprocess.run(command, check=True, capture_output=True, text=True,
                            timeout=NM_TIMEOUT_SECONDS).stdout
    names = {line.split()[-1] for line in output.splitlines() if line.strip()}
    return {name[1:] if darwin and name.startswith("_") else name for name in names}


def check_exports(library: Path) -> None:
    """Fail unless the library exports exactly the public API."""
    exported = exported_symbols(library, sys.platform == "darwin")
    if exported != PUBLIC_API:
        raise ValueError(f"{library} exports {sorted(exported)}, but only the public API "
                         f"{sorted(PUBLIC_API)} may be exported")


def main() -> None:
    """Run one build step from the command line."""
    cli = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    steps = cli.add_subparsers(dest="step", required=True)
    sources = steps.add_parser("sources")
    sources.add_argument("--table", type=Path, required=True)
    sources.add_argument("--release", type=Path, action="append", default=[])
    sources.add_argument("--flag", action="append", default=[], help="a compile flag of the manifest")
    sources.add_argument("--output", type=Path, required=True)
    steps.add_parser("exports").add_argument("library", type=Path)
    arguments = cli.parse_args()
    if arguments.step == "sources":
        library_sources(load_table(arguments.table), arguments.release, arguments.flag, arguments.output)
    else:
        check_exports(arguments.library)


if __name__ == "__main__":
    main()
