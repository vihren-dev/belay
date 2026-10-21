"""Both candidates of ADR 0017's S1, prototype 2, give the Python translation's result
(`belay/sqlite/syntax.py`) for each SQL text of the authored corpora: candidate A, the Lean port
(`packages/belay/Belay/Sqlite/Translation`), and candidate B, the translation in C
(`experiments/surface-s1/candidate-b`).

The authored corpora are the frozen corpora of `judge/claims.json` whose manifest names the
evidence that they cover. Each case gives two texts, as the replay reads them
(`conformance/native_replay.py`): the schema SQL of its initial state and its migration SQL. The
result is the statements with the source range of each node, or the refusal with its status,
message and range; the measurement over all frozen corpora is in `experiments/surface-s1`.
"""

import json
import os
from pathlib import Path
import sys

import pytest

from belay.sqlite.dialects import select_grammar
from belay.sqlite.errors import SqlError
from belay.sqlite.located import Json, Located
from belay.sqlite.parser_library import library_name, load as load_library
from belay.sqlite.sql_tree import SqlParser, parse
from belay.sqlite.syntax import statements
from conformance.corpus import load
from conformance.native_replay import schema_sql
from conformance.record_parser import record_profile
from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, SUFFIX, candidate_b, candidate_b_result, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "measured.sql"
"""The source name of each diagnostic, which both translations report."""
MINIMUM_TEXTS = 1000
"""Fewer texts than the 1,686 of the 42 authored corpora on 2026-10-21: fewer than this means that
the suite's inputs lost corpora, and the comparison would check too little."""


def located(item: Located) -> Json:
    """A located value as JSON: its value, its byte range and its located children."""
    return {"value": item.value, "start": item.start, "end": item.end,
            "children": [located(child) for child in item.children]}


def python_result(parser: SqlParser, sql: str) -> Json:
    """The Python translation's result for one text."""
    try:
        return {"statements": [located(item) for item in statements(parse(parser, sql.encode(), SOURCE))]}
    except SqlError as error:
        return {"refusal": error.diagnostic()}


def authored_texts(runtime_root: Path) -> list[dict[str, Json]]:
    """The grammar, SQL and Python result of each text of the authored corpora."""
    library = load_library(runtime_root / "parser-library/lib" / library_name(sys.platform))
    claims = json.loads((ROOT / "judge/claims.json").read_text())["corpora"]
    texts: list[dict[str, Json]] = []
    for claim in sorted(claims.values(), key=lambda claim: claim["path"]):
        manifest = ROOT / claim["path"] / "manifest.json"
        # The suite's inputs hold only the authored corpora (`authoredCorpora` in `build-support/tests.nix`).
        if not manifest.exists() or "evidenceKind" not in json.loads(manifest.read_text()):
            continue
        directory = manifest.parent
        for record in load(directory)[1]:
            parser = SqlParser(library, select_grammar(library.metadata, record_profile(record)))
            for sql in (schema_sql(record["initial"]["visible"]), record["migrationSql"]):
                texts.append({"grammar": parser.grammar, "sql": sql, "python": python_result(parser, sql)})
    return texts


@pytest.fixture(scope="module")
def texts(runtime_root: Path) -> list[dict[str, Json]]:
    """The texts of the authored corpora with the Python translation's results, read once for both
    candidates."""
    return authored_texts(runtime_root)


def test_lean_translation_equals_python_translation(runtime_root: Path, tmp_path: Path,
                                                    texts: list[dict[str, Json]]) -> None:
    """For each text of the authored corpora, the Lean port's statements, ranges and refusals are
    the Python translation's (`tests/surface/TranslationEquality.lean` compares them)."""
    assert len(texts) > MINIMUM_TEXTS and any("refusal" in text["python"] for text in texts)  # type: ignore[operator]
    path = tmp_path / "texts.jsonl"
    path.write_text("".join(json.dumps(text) + "\n" for text in texts))
    result = run_command(surface_command(runtime_root, FIXTURES / "TranslationEquality.lean", tmp_path), cwd=tmp_path,
                         environment={**os.environ, "BELAY_TRANSLATION_TEXTS": str(path)}, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    assert f"texts {len(texts)} different 0" in result.stdout, result.diagnostic()


def test_c_translation_equals_python_translation(runtime_root: Path, texts: list[dict[str, Json]]) -> None:
    """For each text of the authored corpora, candidate B's statements, ranges and refusals are the
    Python translation's; the JSON compares with sorted keys, so `true` and `1` differ."""
    library = candidate_b(runtime_root / f"candidate-b/lib/libtranslate-b{SUFFIX}")
    different = [text["sql"] for text in texts if json.dumps(candidate_b_result(library, text["grammar"], text["sql"]),
                                                               sort_keys=True) != json.dumps(text["python"], sort_keys=True)]
    assert len(texts) > MINIMUM_TEXTS and not different, different[:5]
