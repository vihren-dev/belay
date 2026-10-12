"""The verdict of one case: the subject's prediction against the recorded observations.

The order of the checks follows the verdict rules that `classifyCase` in
`VerifierConformance/Case.lean` applied before the judge existed: the initial state first,
then the subject's own scope, then each executed statement, then the statement outputs.
"""

from dataclasses import dataclass

from judge.catalog import step_form
from judge.cells import Json
from judge.outputs import matches_output
from judge.records import WITH_OUTPUTS, recorded_steps

VERDICTS = ("AGREE", "DISAGREE", "MODEL_UNSUPPORTED", "HARNESS_ERROR")
"""Every verdict that the judge gives."""
SQLITE_ERROR = 1
"""SQLite's primary result code for an SQL error, such as a syntax error."""


@dataclass(frozen=True)
class Verdict:
    """The verdict of one case; `position` is the first statement that differs, if any."""

    name: str
    position: int | None = None
    detail: str = ""


def same_step(recorded: dict[str, Json], predicted: dict[str, Json]) -> bool:
    """Whether a predicted step has the recorded tables, transaction state and result code."""
    return step_form(recorded) == step_form(predicted)


def compare_outputs(record: dict[str, Json], outputs: list[Json]) -> Verdict:
    """Compare the outputs of the executed statements, one per recorded statement."""
    for position, event in enumerate(record["trace"]):
        if position >= len(outputs) or not isinstance(outputs[position], dict):
            return Verdict("DISAGREE", position, "missing predicted output")
        if not matches_output(event, outputs[position], event.get("groups")):
            return Verdict("DISAGREE", position, "output differs")
    if len(outputs) != len(record["trace"]):
        return Verdict("DISAGREE", len(record["trace"]), "extra predicted output")
    return Verdict("AGREE")


def consumed_ranges(record: dict[str, Json]) -> list[tuple[int, int]]:
    """The byte range of the migration SQL that SQLite consumed for each executed statement."""
    migration, offset, ranges = record["migrationSql"].encode(), 0, []
    for event in record["trace"]:
        consumed = event["sql"].encode()
        if migration[offset:offset + len(consumed)] != consumed:
            raise ValueError("recorded statement text is not the next part of the migration SQL")
        ranges.append((offset, offset + len(consumed)))
        offset += len(consumed)
    return ranges


def boundary_differs(ranges: list[tuple[int, int]], steps: list[dict[str, Json]], position: int) -> bool:
    """Whether the predicted statement does not start inside SQLite's consumed range, or the
    next predicted statement starts before that range ends."""
    begin, end = ranges[position]
    start = steps[position + 1]["start"]
    following = steps[position + 2]["start"] if position + 2 < len(steps) else None
    return type(start) is not int or not begin <= start < end or (type(following) is int and following < end)


def predicted_verdict(record: dict[str, Json], prediction: dict[str, Json]) -> Verdict:
    """The verdict of a prediction with observations."""
    steps, recorded, ranges = prediction["steps"], recorded_steps(record), consumed_ranges(record)
    if not isinstance(steps, list) or not steps:
        raise ValueError("a prediction has no initial step")
    if not same_step(recorded[0], steps[0]):
        return Verdict("DISAGREE", None, "initial state differs")
    outputs = prediction.get("outputs", [])
    if not prediction["supported"] or (record.get("nativeVersion") in WITH_OUTPUTS
                                       and any(output is None for output in outputs)):
        return Verdict("MODEL_UNSUPPORTED", None, "the subject declares this case out of its scope")
    for position in range(max(len(steps), len(recorded)) - 1):
        if position + 1 >= len(steps) or position + 1 >= len(recorded):
            return Verdict("DISAGREE", position, "different number of executed statements")
        event, step = recorded[position + 1], steps[position + 1]
        if boundary_differs(ranges, steps, position):
            return Verdict("DISAGREE", position, "different statement boundary")
        if not same_step(event, step):
            return Verdict("DISAGREE", position, "observation differs")
    if record.get("nativeVersion") in WITH_OUTPUTS:
        return compare_outputs(record, outputs)
    return Verdict("AGREE")


def case_verdict(record: dict[str, Json], prediction: Json) -> Verdict:
    """The verdict of one case. A malformed record or prediction is a harness error."""
    try:
        if not isinstance(prediction, dict) or prediction.get("name") != record["name"]:
            raise ValueError("the prediction is missing or names another case")
        status = prediction["status"]
        if status == "unsupported":
            return Verdict("MODEL_UNSUPPORTED", None, str(prediction.get("reason", "")))
        if status == "inputError":
            trace = record["trace"]
            if trace and trace[-1].get("primaryCode") == SQLITE_ERROR:
                return Verdict("MODEL_UNSUPPORTED", None, "SQLite also refused the SQL")
            return Verdict("DISAGREE", None, "the frontend refused SQL that SQLite ran")
        if status != "predicted":
            raise ValueError(f"unknown prediction status {status!r}")
        return predicted_verdict(record, prediction)
    except (KeyError, TypeError, ValueError, IndexError) as error:
        return Verdict("HARNESS_ERROR", None, f"{type(error).__name__}: {error}")
