"""`python -m conformance.predict --runtime ROOT`: the subject's predict command (ADR 0011).

The judge (`judge/`) writes one input per line: what a frozen record holds before its
migration runs. This command translates each input with the frontend, runs the model's
`conformance-runner --predict` once over all translated inputs, and writes one prediction per
line in the recorded form (`conformance.predict_render`). It never sees an observation that
SQLite made after the start, and it decides nothing about agreement.
"""

import argparse
from collections.abc import Sequence
import json
from pathlib import Path
import subprocess
import sys

from belay.sqlite.admission import admit
from belay.sqlite.dialects import NoParserForDialect
from belay.sqlite.errors import SqlError
from belay.sqlite.sql_model import Statement, Table
from belay.sqlite.sql_tree import ParserResourceLimit, parse
from belay.sqlite.translate import starting_schema, statements
from conformance import native_bindings
from conformance.case_format import Json, schema_wire, statement_wire, table_wire
from conformance.predict_render import output_record, view_record
from conformance.record_parser import NO_PARSER_REASON, record_parser, runtime_library

RUNNER_TIMEOUT_SECONDS = 600
"""One model run over all inputs of a corpus."""
PROFILE_VERSION = 4
"""Native record version whose execution profiles the model does not implement yet."""


def initial_tables(schema: tuple[Table, ...], rows: dict[str, Json]) -> list[Json]:
    """The starting tables: the translated schema with the given rows, by table name."""
    by_name = {name.lower(): table_rows for name, table_rows in rows.items()}
    return [[table.name, table_wire(table, [
        (native_bindings.decode_cell(row["identity"][0])[1], tuple(native_bindings.decode_cell(cell) for cell in row["values"]))
        for row in by_name.get(table.name, [])])] for table in sorted(schema, key=lambda item: item.name)]


def translated(given: dict[str, Json], library: object) -> tuple[dict[str, Json], list[Statement]]:
    """The model input of one case and its statements; frontend refusals raise `SqlError`."""
    if given.get("nativeVersion") == PROFILE_VERSION:
        raise SqlError("UNSUPPORTED", f"{given['name']}: the model does not implement execution profiles "
                       f"(native record version {PROFILE_VERSION}); this case stays out of scope until it does")
    parser = record_parser(library, given)
    schema = starting_schema(parse(parser, given["initialSchemaSql"].encode(), "corpus-schema.sql"))
    script = statements(parse(parser, given["migrationSql"].encode(), "corpus-migration.sql"))
    admit(schema, script)
    return {"schema": [schema_wire(table) for table in schema], "initial": initial_tables(schema, given["initialRows"]),
            "script": [statement_wire(statement) for statement in script]}, script


def refusal(given: dict[str, Json], error: Exception) -> dict[str, Json]:
    """The prediction of a case that the frontend refuses: out of scope, or an input error."""
    if isinstance(error, NoParserForDialect):
        return {"name": given["name"], "status": "unsupported", "reason": NO_PARSER_REASON}
    if isinstance(error, SqlError) and error.status == "UNSUPPORTED":
        return {"name": given["name"], "status": "unsupported", "reason": str(error)}
    migration = isinstance(error, SqlError) and error.source == "corpus-migration.sql"
    if migration and (error.status == "INPUT_ERROR" or isinstance(error, ParserResourceLimit)):
        return {"name": given["name"], "status": "inputError", "reason": str(error)}
    return {"name": given["name"], "status": "error", "reason": f"{type(error).__name__}: {error}"}


def prediction(given: dict[str, Json], script: list[Statement], model: dict[str, Json]) -> dict[str, Json]:
    """One prediction in the recorded form. Bound parameters are outside the model's scope."""
    if "error" in model:
        return {"name": given["name"], "status": "error", "reason": str(model["error"])}
    steps = [{"visible": view_record(step["visible"]), "persisted": view_record(step["persisted"]),
              "transactionOpen": step["transactionOpen"], "primaryCode": step["primaryCode"],
              **({"start": script[index - 1].start} if index else {})}
             for index, step in enumerate(model["steps"])]
    parameters = given.get("parameters", [])
    return {"name": given["name"], "status": "predicted",
            "supported": bool(model["supported"]) and not any(values for values in parameters),
            "steps": steps, "outputs": [output_record(output) for output in model["outputs"]]}


def main(arguments: Sequence[str]) -> int:
    """Predict every input on standard input, in order, one line each."""
    parser = argparse.ArgumentParser(prog="python -m conformance.predict", description=main.__doc__)
    parser.add_argument("--runtime", type=Path, required=True, help="conformance runtime root")
    options = parser.parse_args(arguments)
    library = runtime_library(options.runtime)
    inputs = [json.loads(line) for line in sys.stdin if line.strip()]
    results: list[dict[str, Json] | None] = []
    pending: list[tuple[int, list[Statement], dict[str, Json]]] = []
    for index, given in enumerate(inputs):
        try:
            model_input, script = translated(given, library)
            pending.append((index, script, model_input))
            results.append(None)
        except (SqlError, NoParserForDialect, ValueError, KeyError, TypeError, IndexError) as error:
            results.append(refusal(given, error))
    runner = options.runtime / ".lake/build/bin/conformance-runner"
    answered = subprocess.run([str(runner), "--predict"], input="".join(json.dumps(item[2]) + "\n" for item in pending),
                              capture_output=True, text=True, timeout=RUNNER_TIMEOUT_SECONDS, check=False)
    if answered.returncode:
        print(f"predict: {runner} exited with {answered.returncode}: {answered.stderr.strip()}. Read the "
              f"runner's message above, rebuild the conformance runtime (nix-build build-support/default.nix "
              f"-A conformance), and run the command again.", file=sys.stderr)
        return 1
    for (index, script, _), line in zip(pending, answered.stdout.splitlines(), strict=True):
        results[index] = prediction(inputs[index], script, json.loads(line))
    for result in results:
        print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
