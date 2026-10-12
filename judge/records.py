"""Read frozen corpora and split each record into the subject's input and the recorded truth.

The subject input holds only what exists before the migration runs: the profile, the
initial schema SQL and rows, the migration SQL and the statement parameters. Every later
observation stays with the judge, so the subject cannot copy the answer.
"""

from collections.abc import Iterator
import gzip
import json
from pathlib import Path

from judge.cells import Json, text

CASES_FILE = "cases.jsonl.gz"
"""Corpora v1 to v3 store one record per line in this file."""


def corpus_records(directory: Path) -> Iterator[dict[str, Json]]:
    """The records of one frozen corpus, in stored order."""
    path = directory / CASES_FILE
    if not path.is_file():
        raise ValueError(f"{directory}: no {CASES_FILE}; this corpus layout is not supported yet")
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        for line in stream:
            if line.strip():
                record = json.loads(line)
                if not isinstance(record, dict):
                    raise ValueError(f"{path}: a record is not a JSON object")
                yield record


def schema_sql(observation: dict[str, Json]) -> str:
    """The recorded `sqlite_schema` SQL, tables first, as the input that recreates the state.

    SQLite lists indexes before tables; the input must declare a table before its index.
    Objects without SQL (automatic indexes) are left out, as SQLite creates them itself.
    """
    rows = observation["schema"]
    if not isinstance(rows, list):
        raise ValueError("recorded schema is not a list")
    ordered = sorted(rows, key=lambda row: text(row[0]) != "table")
    return "\n".join(text(row[3]) + ";" for row in ordered if row[3] != "null")


def initial_rows(observation: dict[str, Json]) -> dict[str, Json]:
    """The recorded rows of each initial table, by table name, as the subject's starting data."""
    tables = observation["tables"]
    if not isinstance(tables, list):
        raise ValueError("recorded tables are not a list")
    return {table["name"]: [{"identity": row["identity"], "values": row["values"]} for row in table["rows"]]
            for table in tables}


def subject_input(record: dict[str, Json]) -> dict[str, Json]:
    """What the subject may see of one record: nothing that was observed after the start."""
    trace = record["trace"]
    if not isinstance(trace, list):
        raise ValueError("recorded trace is not a list")
    initial = record["initial"]["visible"]
    given: dict[str, Json] = {"name": record["name"], "nativeVersion": record.get("nativeVersion"),
                              "profile": record.get("profile"), "initialSchemaSql": schema_sql(initial),
                              "initialRows": initial_rows(initial), "migrationSql": record["migrationSql"]}
    if record.get("nativeVersion") in (3, 4):
        # Bound parameters are statement inputs. Their list has one entry per executed statement,
        # which tells the subject how far SQLite got; records before version 3 have none.
        given["parameters"] = [event["parameters"] for event in trace]
    return given


def recorded_steps(record: dict[str, Json]) -> list[dict[str, Json]]:
    """The recorded initial observation and one observation per executed statement."""
    return [record["initial"], *record["trace"]]
