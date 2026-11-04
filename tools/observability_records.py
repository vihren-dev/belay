"""Validate immutable execution artifacts and wrap native reportlog events (ADR 0028)."""

from collections.abc import Iterator
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from uuid import UUID, uuid5

MAX_LINE = 8 * 1024 * 1024
"""Reject oversized records before decoding; retain the artifact for diagnosis."""


def diagnostic(message: str) -> None:
    """Keep delivery diagnostics distinct from test results."""
    print(f"Observability: {message}", file=sys.stderr, flush=True)


def json_object(raw: str | bytes) -> dict[str, object]:
    """Accept JSON objects only, including at the untrusted CI artifact boundary."""
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError("expected a JSON object")
    return value


def encode(value: object) -> str:
    """Use strict JSON for both embedded objects and outer JSONEachRow rows."""
    return json.dumps(value, ensure_ascii=True, allow_nan=False, separators=(",", ":"))


def execution(directory: Path) -> dict[str, object]:
    """Validate the manifest and normalize its UTC timestamp for ClickHouse."""
    raw = (directory / "execution.json").read_bytes()
    if len(raw) > MAX_LINE:
        raise ValueError("execution manifest exceeds 8 MiB")
    value = json_object(raw)
    identity = str(UUID(str(value["execution_id"])))
    started = datetime.fromisoformat(str(value["started_at"]))
    if started.tzinfo is None:
        raise ValueError("started_at must have a UTC offset")
    metadata = value.get("metadata", {})
    if not isinstance(metadata, dict):
        raise ValueError("metadata must be an object")
    return {"execution_id": identity,
            "started_at": started.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S.%f"),
            "metadata": encode(metadata)}


def events(directory: Path, identity: str, *, warn: bool = True) -> Iterator[dict[str, object]]:
    """Keep original line positions; omit only an unterminated last line of a stopped producer."""
    finished = False
    with (directory / "report.jsonl").open("rb") as stream:
        number = 0
        while raw := stream.readline(MAX_LINE + 1):
            number += 1
            if len(raw) > MAX_LINE:
                raise ValueError(f"report line {number} exceeds 8 MiB")
            if not raw.endswith(b"\n"):
                if warn:
                    diagnostic(f"{directory}: excluded unterminated final line {number}")
                break
            data = json_object(raw)
            kind = data.get("$report_type")
            node = data.get("nodeid")
            if not isinstance(kind, str) or (node is not None and not isinstance(node, str)):
                raise ValueError(f"invalid kind or nodeid at line {number}")
            finished |= kind == "SessionFinish"
            yield {"execution_id": identity, "event_id": str(uuid5(UUID(identity), str(number))),
                   "test_node_id": node, "kind": kind, "data": encode(data)}
    if not finished and warn:
        diagnostic(f"{directory}: incomplete session (no SessionFinish)")
