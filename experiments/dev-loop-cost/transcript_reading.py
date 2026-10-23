"""Read a Claude Code session transcript (JSON lines) into the facts that a cost report needs.

Each API request appears once, with its context size; each tool call has a category,
and each tool result its size in tokens and the request after which it entered the
context. `token_drivers.py` turns these facts into the report.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path

CHARACTERS_PER_TOKEN = 4


# First match wins, so the specific categories come before the general ones.
BASH_CATEGORIES: list[tuple[str, re.Pattern[str]]] = [
    ("review", re.compile(r"\bjust review")),
    ("nix build/test", re.compile(r"nix-build|nix build|nix develop|\bjust (test|build|package|check|verdict)")),
    # A command `lake` or `lean`, not a `.lean` path in a `cat` or `grep` command.
    ("lean/lake", re.compile(r"(?:^|[\s;&|(]|/bin/)(?:lake|lean)(?=\s)")),
    ("wait/poll", re.compile(r"\bsleep\b|gh run (watch|view)|gh pr checks|\bwait\b")),
    ("jj/git/gh", re.compile(r"\bjj\b|\bgit\b|\bgh\b")),
    ("python/pytest", re.compile(r"python|pytest")),
    ("read/search", re.compile(r"^\s*(cd [^;&]+(&&|;)\s*)?(cat|sed|head|tail|grep|rg|ugrep|ls|find|wc|diff)\b")),
]


@dataclass
class Request:
    """One API request: its context size and token use, deduplicated by request id."""
    index: int
    context: int
    cache_read: int
    cache_write: int
    output: int
    uncached_input: int


def bash_category(command: str) -> str:
    """Return the category of a shell command, by the first matching pattern."""
    for name, pattern in BASH_CATEGORIES:
        if pattern.search(command):
            return name
    return "bash other"


def tool_category(name: str, tool_input: dict[str, object]) -> str:
    """Return the category of one tool call."""
    if name == "Bash":
        return bash_category(str(tool_input.get("command", "")))
    if name in ("Read", "Grep", "Glob"):
        return "read/search"
    if name in ("Edit", "Write", "MultiEdit"):
        return "edit"
    if name in ("Agent", "Task"):
        return "subagent"
    if name in ("TaskOutput", "BashOutput", "Monitor", "ScheduleWakeup"):
        return "wait/poll"
    return "other tools"


def result_text_length(content: object) -> int:
    """Return the number of characters of a tool result's content."""
    if isinstance(content, str):
        return len(content)
    if isinstance(content, list):
        return sum(len(str(block.get("text", ""))) if isinstance(block, dict) else len(str(block)) for block in content)
    return len(str(content))


def is_human_prompt(record: dict[str, object]) -> str | None:
    """Return the text of a prompt that a person typed, or None for tool results and meta records."""
    if record.get("type") != "user" or record.get("isMeta") or record.get("isCompactSummary"):
        return None
    content = record["message"]["content"]  # type: ignore[index]
    if isinstance(content, str):
        text = content
    else:
        if any(isinstance(b, dict) and b.get("type") == "tool_result" for b in content):
            return None
        text = " ".join(str(b.get("text", "")) for b in content if isinstance(b, dict))
    if text.startswith("<") or "Caveat:" in text[:40]:
        return None
    return text


def timestamp_seconds(record: dict[str, object]) -> float:
    """Return the record's timestamp in seconds since the epoch."""
    return datetime.fromisoformat(str(record["timestamp"]).replace("Z", "+00:00")).timestamp()


def usage_totals(path: Path) -> tuple[int, int, int, int]:
    """Return cache read, cache write, output and uncached input of one transcript."""
    seen: set[str] = set()
    totals = [0, 0, 0, 0]
    with path.open() as stream:
        for line in stream:
            record = json.loads(line)
            if record.get("type") != "assistant" or "usage" not in record.get("message", {}):
                continue
            request_id = record.get("requestId") or record["uuid"]
            if request_id in seen:
                continue
            seen.add(request_id)
            usage = record["message"]["usage"]
            totals[0] += usage.get("cache_read_input_tokens", 0)
            totals[1] += usage.get("cache_creation_input_tokens", 0)
            totals[2] += usage.get("output_tokens", 0)
            totals[3] += usage.get("input_tokens", 0)
    return totals[0], totals[1], totals[2], totals[3]


@dataclass
class Session:
    """The facts of one transcript that the report needs, in request order."""
    requests: list[Request] = field(default_factory=list)
    compactions: list[int] = field(default_factory=list)  # index of the first request after each
    prompts: list[tuple[int, int]] = field(default_factory=list)  # (first request index, prompt tokens)
    notifications: int = 0  # requests started by a background-task notification
    results: list[tuple[str, int, int, float]] = field(default_factory=list)  # category, tokens, index, seconds
    inputs: list[tuple[str, int, int]] = field(default_factory=list)  # tool name, input tokens, index


def read_session(path: Path) -> Session:
    """Read a transcript into a Session."""
    session = Session()
    seen: set[str] = set()
    pending: dict[str, tuple[str, float]] = {}
    with path.open() as stream:
        for line in stream:
            record = json.loads(line)
            kind = record.get("type")
            if kind == "system" and record.get("subtype") == "compact_boundary":
                session.compactions.append(len(session.requests))
            elif kind == "assistant":
                message = record["message"]
                for block in message.get("content", []):
                    if isinstance(block, dict) and block.get("type") == "tool_use":
                        pending[block["id"]] = (tool_category(block["name"], block.get("input", {})),
                                                timestamp_seconds(record))
                        session.inputs.append((block["name"], len(json.dumps(block.get("input", {}))) // CHARACTERS_PER_TOKEN,
                                               len(session.requests)))
                request_id = record.get("requestId") or record["uuid"]
                if "usage" in message and request_id not in seen:
                    seen.add(request_id)
                    u = message["usage"]
                    read, write, uncached = (u.get("cache_read_input_tokens", 0),
                                             u.get("cache_creation_input_tokens", 0), u.get("input_tokens", 0))
                    session.requests.append(Request(len(session.requests), read + write + uncached,
                                                    read, write, u.get("output_tokens", 0), uncached))
            elif kind == "user":
                content = record["message"]["content"]
                if isinstance(content, list):
                    for block in content:
                        if isinstance(block, dict) and block.get("type") == "tool_result":
                            category, started = pending.pop(block.get("tool_use_id"), ("unknown", 0.0))
                            tokens = result_text_length(block.get("content")) // CHARACTERS_PER_TOKEN
                            seconds = timestamp_seconds(record) - started if started else 0.0
                            session.results.append((category, tokens, len(session.requests), seconds))
                text = is_human_prompt(record)
                if text is not None:
                    session.prompts.append((len(session.requests), len(text) // CHARACTERS_PER_TOKEN))
                elif isinstance(content, str) and content.startswith("<task-notification"):
                    session.notifications += 1
    return session

