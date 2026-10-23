"""Write the SQL texts of the frozen corpora, with the Python frontend's parse time and
translation of each, for the measurements of ADR 0017, S1 (`README.md`).

Each case of a frozen corpus (`judge/claims.json`) gives two texts, as the replay reads them
(`conformance/native_replay.py`): the schema SQL of its initial state and its migration SQL.
Each line of the output is one text: the corpus, the case, the role, the grammar identity of
the case's dialect, the SQL, the seconds of the Python binding's parse, and the Python
translation's result: the statements with the source range of each node, or the refusal.

Run from the repository root: `python3 experiments/surface-s1/texts.py RUNTIME FOLDER`, with the
conformance runtime root. It writes `texts.jsonl` and `sql.jsonl`, the grammar and the SQL of each
text, which the parse time measurements read.
"""

import json
from pathlib import Path
import sys
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from belay.sqlite.errors import SqlError  # noqa: E402
from belay.sqlite.located import Json, Located  # noqa: E402
from belay.sqlite.sql_tree import parse  # noqa: E402
from belay.sqlite.syntax import statements  # noqa: E402
from conformance.corpus import load  # noqa: E402
from conformance.native_replay import schema_sql  # noqa: E402
from conformance.record_parser import record_parser, runtime_library  # noqa: E402


def located(item: Located) -> Json:
    """A located value as JSON: its value, its byte range and its located children."""
    return {"value": item.value, "start": item.start, "end": item.end,
            "children": [located(child) for child in item.children]}


def translation(parser: object, sql: str) -> tuple[float, Json]:
    """The Python binding's parse time of the text and the translation's result."""
    started = perf_counter()
    try:
        tree = parse(parser, sql.encode(), "measured.sql")  # type: ignore[arg-type]
    except SqlError as error:
        return perf_counter() - started, {"refusal": error.diagnostic()}
    seconds = perf_counter() - started
    try:
        return seconds, {"statements": [located(item) for item in statements(tree)]}
    except SqlError as error:
        return seconds, {"refusal": error.diagnostic()}


def main() -> None:
    """Write one JSON line for each text of each frozen corpus, to both files."""
    runtime, folder = Path(sys.argv[1]), Path(sys.argv[2])
    output = folder / "texts.jsonl"
    library = runtime_library(runtime)
    claims = json.loads(Path("judge/claims.json").read_text())["corpora"]
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w") as lines, (folder / "sql.jsonl").open("w") as sql_lines:
        for corpus, claim in sorted(claims.items()):
            _, records = load(Path(claim["path"]))
            for record in records:
                name = str(record.get("name", ""))
                try:
                    parser = record_parser(library, record)
                    texts = [("schema", schema_sql(record["initial"]["visible"])), ("migration", record["migrationSql"])]
                except (KeyError, ValueError, TypeError, SqlError) as error:
                    lines.write(json.dumps({"corpus": corpus, "case": name, "skipped": str(error)}) + "\n")
                    continue
                for role, sql in texts:
                    seconds, result = translation(parser, sql)
                    lines.write(json.dumps({"corpus": corpus, "case": name, "role": role, "grammar": parser.grammar,
                                            "sql": sql, "pythonSeconds": seconds, "python": result}) + "\n")
                    sql_lines.write(json.dumps({"grammar": parser.grammar, "sql": sql}) + "\n")


if __name__ == "__main__":
    main()
