"""The translation program of the text package (`packages/belay-sqlite-text/TranslationProgram.lean`
and `Belay/Sqlite/TranslationRequest.lean`) answers a batch of requests, one JSON line for each,
in one process: the harness sends all SQL texts of a corpus through it.
"""

import json
from pathlib import Path
import subprocess

import pytest

from conformance.native_library import DEFAULT_ENGINE_VERSION, SOURCE_ID
from tests.runtime_fixtures import require_file

pytestmark = [pytest.mark.integration, pytest.mark.parser]

SOURCE = "batch.sql"
"""The source name of each request, which each refusal reports."""


def request(sql: bytes, version: str = DEFAULT_ENGINE_VERSION) -> str:
    """One request line for the SQL bytes under the build of the default native library."""
    return json.dumps({"profile": {"version": version, "sourceId": SOURCE_ID, "compileOptions": []},
                       "source": SOURCE, "sqlHex": sql.hex()}) + "\n"


def answers(runtime_root: Path, batch: str) -> list[dict[str, object]]:
    """The program's answer lines for a batch; the program exits with 0 after the last request."""
    program = require_file(runtime_root / ".lake/build/bin/belay-sqlite-translate", executable=True)
    result = subprocess.run([str(program)], input=batch, capture_output=True, text=True, timeout=30, check=False)
    assert result.returncode == 0, result.stderr
    return [json.loads(line) for line in result.stdout.splitlines()]


def refusal(status: str, start: int, end: int, message: str) -> dict[str, object]:
    """A refusal of the batch's source."""
    return {"status": status, "message": message, "source": SOURCE, "start": start, "end": end}


GRAMMAR_ERROR = "SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again"
LIMIT = ("SQL exceeds the parser's limits of 1 MiB of input and 200,000 syntax-tree nodes; "
         "split the SQL into smaller files")


def test_one_process_answers_each_request_of_a_batch(runtime_root: Path) -> None:
    """Each request gets its line, in order, and a failed request does not stop the batch:
    statements with their values, ranges and commands; a grammar error at its offset; a model
    refusal with the commands that the grammar found; bytes that are not UTF-8, which the parser
    library rejects at offset 0; a text over the parser's limits; a release without a grammar; and
    a line that is not a request."""
    batch = (request(b"COMMIT;") + request(b"SELECT * FORM t;") + request(b"VACUUM; PRAGMA table_info(t);")
             + request(b"SELECT 'a\xff';") + request(b" " * (1024 * 1024 + 1)) + request(b"COMMIT;", "3.45.0")
             + "not a request\n")
    lines = answers(runtime_root, batch)
    assert len(lines) == 7, lines
    assert lines[0] == {"result": "statements", "statements": [{"value": "commit", "start": 0, "end": 6}],
                        "commands": [{"symbols": ["COMMIT", "trans_opt"], "names": []}]}
    assert lines[1] == {"result": "parseRefusal", "refusal": refusal("INPUT_ERROR", 9, 0, GRAMMAR_ERROR)}
    assert lines[2]["result"] == "translationRefusal"
    assert lines[2]["refusal"]["status"] == "UNSUPPORTED" and lines[2]["refusal"]["end"] == 6
    assert lines[2]["commands"] == [{"symbols": ["VACUUM", "vinto"], "names": []},
                                    {"symbols": ["PRAGMA", "nm", "dbnm", "LP", "nmnum", "RP"], "names": ["table_info"]}]
    assert lines[3] == {"result": "parseRefusal", "refusal": refusal("INPUT_ERROR", 0, 0, GRAMMAR_ERROR)}
    assert lines[4]["result"] == "limit" and lines[4]["refusal"]["message"] == LIMIT
    assert lines[5]["result"] == "noParser" and "has no SQLite 3.45.0" in lines[5]["message"]
    assert lines[6]["result"] == "error" and "the request is not usable" in lines[6]["message"]


def test_a_wrapper_has_no_commands(runtime_root: Path) -> None:
    """The grammar's commands are `null` when a wrapper such as EXPLAIN wraps one, because the
    harness's query diagnostic leaves such a text out; the refusal names the wrapper."""
    [answer] = answers(runtime_root, request(b"EXPLAIN SELECT 1;"))
    assert answer["result"] == "translationRefusal" and answer["commands"] is None
    assert "command wrapper, such as EXPLAIN" in answer["refusal"]["message"]
