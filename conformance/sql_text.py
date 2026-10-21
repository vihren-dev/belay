"""The harness's client of the text package's translation program (`belay-sqlite-translate`).

The program parses SQL text with the parser library's grammar of an execution profile and
translates it to the model's statement syntax (`packages/belay-sqlite-text`). The harness keeps
one program process for each runtime and process ID, sends one request line for each text and
reads its answer line, so a corpus costs one process start. The refusals are the `SqlError`s of
the frontend: a grammar error (`INPUT_ERROR`), the parser's limits (`ParserResourceLimit`), a
statement that the model does not run (`UNSUPPORTED`), and a profile without a grammar
(`NoParserForDialect`).
"""

from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
from typing import IO

from belay.sqlite.dialects import ProfileIdentity
from belay.sqlite.errors import NoParserForDialect, ParserResourceLimit, SqlError
from belay.sqlite.located import Json, Located

PROGRAM = ".lake/build/bin/belay-sqlite-translate"
"""The translation program in a conformance runtime root."""


@dataclass(frozen=True)
class Command:
    """One command that the grammar found: the symbols of its parts, and the text of each `nm`
    part, such as a PRAGMA's name."""

    symbols: tuple[str, ...]
    names: tuple[str, ...]


def refusal(answer: dict[str, Json]) -> SqlError:
    """The `SqlError` of a refusal answer, with its status, message, source and range."""
    item = answer["refusal"]
    assert isinstance(item, dict)
    if answer["result"] == "limit":
        return ParserResourceLimit(str(item["source"]), int(item["start"]))  # type: ignore[arg-type]
    return SqlError(item["status"], str(item["message"]), source=str(item["source"]),  # type: ignore[arg-type]
                    start=int(item["start"]), end=int(item["end"]))  # type: ignore[arg-type]


@dataclass(frozen=True)
class Translation:
    """The program's answer for one text: the refusal of its parse, or the grammar's commands and
    the statements or the translation's refusal."""

    answer: dict[str, Json]

    def parsed(self) -> "Translation":
        """Return this translation; raise the refusal of a text that the parser rejects."""
        if self.answer["result"] in ("parseRefusal", "limit"):
            raise refusal(self.answer)
        return self

    def statements(self) -> tuple[Located, ...]:
        """Return each statement's value and byte range; raise the parse or translation refusal."""
        if self.parsed().answer["result"] == "translationRefusal":
            raise refusal(self.answer)
        items = self.answer["statements"]
        assert isinstance(items, list)
        return tuple(Located(item["value"], item["start"], item["end"]) for item in items)  # type: ignore[index, arg-type]

    def commands(self) -> tuple[Command, ...] | None:
        """Return the grammar's commands, or `None` for a wrapper such as EXPLAIN; raise the parse
        refusal."""
        found = self.parsed().answer["commands"]
        if found is None:
            return None
        assert isinstance(found, list)
        return tuple(Command(tuple(item["symbols"]), tuple(item["names"])) for item in found)  # type: ignore[index, arg-type]


class Translator:
    """One process of the translation program of a runtime root."""

    def __init__(self, runtime: Path) -> None:
        """Start the program; it answers until its standard input closes."""
        self.program = runtime / PROGRAM
        if not self.program.is_file():
            raise RuntimeError(f"The translation program is missing: {self.program}; build the conformance runtime "
                               "(nix-build build-support/default.nix -A conformance) and run the command again")
        self.process = subprocess.Popen([str(self.program)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, text=True, encoding="utf-8")

    def answer(self, profile: ProfileIdentity, sql: bytes, source: str) -> dict[str, Json]:
        """Send one request and read its answer line."""
        stdin, stdout = self.process.stdin, self.process.stdout
        assert stdin is not None and stdout is not None
        request = {"profile": {"version": profile.version, "sourceId": profile.source_id,
                               "compileOptions": list(profile.compile_options)}, "source": source, "sqlHex": sql.hex()}
        try:
            stdin.write(json.dumps(request) + "\n")
            stdin.flush()
        except BrokenPipeError:
            pass
        line = stdout.readline()
        if not line:
            raise RuntimeError(f"The translation program {self.program} stopped: {stopped(self.process.stderr)}. "
                               "Rebuild the conformance runtime and run the command again")
        return json.loads(line)


def stopped(stderr: IO[str] | None) -> str:
    """The program's error output after it stopped, or a note that it wrote none."""
    text = stderr.read().strip() if stderr is not None else ""
    return text or "it wrote no error"


TRANSLATORS: dict[tuple[int, Path], Translator] = {}
"""The program process of each process ID and runtime root; a forked worker starts its own."""


def runtime_translator(runtime: Path) -> Translator:
    """The program process of the runtime root for this process."""
    key = (os.getpid(), runtime.resolve())
    if key not in TRANSLATORS:
        TRANSLATORS[key] = Translator(key[1])
    return TRANSLATORS[key]


@dataclass(frozen=True)
class TextParser:
    """The translation of one execution profile's texts."""

    translator: Translator
    profile: ProfileIdentity

    @classmethod
    def for_profile(cls, translator: Translator, profile: ProfileIdentity) -> "TextParser":
        """The parser of a profile; refuse a profile without a grammar in the parser library.
        An empty text checks the profile, because the program selects the grammar for each text."""
        parser = cls(translator, profile)
        parser.translate(b"", "profile-check.sql")
        return parser

    def translate(self, sql: bytes, source: str) -> Translation:
        """The translation of the text, as its bytes, with the source name of its refusals."""
        answer = self.translator.answer(self.profile, sql, source)
        if answer["result"] == "noParser":
            raise NoParserForDialect(str(answer["message"]))
        if answer["result"] == "error":
            raise SqlError("UNVERIFIED", f"The translation program cannot translate the text: {answer['message']}",
                           source=source)
        return Translation(answer)
