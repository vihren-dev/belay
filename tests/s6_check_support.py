"""Helpers of the tests that read the output of the labelled `#sql_check` commands of `tests/surface`."""

import re
from pathlib import Path

from tests.surface_replay_test import native_replay, native_rows

CHAIN_TIMEOUT_SECONDS = 400
"""The time limit of one fixture module, in seconds."""

CHAIN_TEST_TIMEOUT_SECONDS = 600
"""The `pytest-timeout` limit of a test that compiles a chain of fixture modules, in seconds.

The usual limit of 300 seconds ended the module fixture of `surface_s6_check_programs_test`
on the CI runner, where its chain of four modules took 358 seconds."""


def split_blocks(output: str) -> dict[str, str]:
    """The text of each labelled command in the output of a fixture module."""
    return dict(re.findall(r"SQL-COMMAND-BEGIN ([\w-]+)\n(.*?)\nSQL-COMMAND-END \1:", output, re.DOTALL))


def replays(block: str) -> list[str]:
    """The SQLite scripts of the replays of one block, in order."""
    return [part.split("\nDatabase construction:", 1)[0] for part in block.split("SQLite replay:\n")[1:]]


def final_rows(sqlite: str, directory: Path, name: str, script: str, inspect: str) -> list[list[object]]:
    """Run one replay script in native SQLite and read the rows that the inspection query gives."""
    result = native_replay(sqlite, script, directory, name, inspect=inspect)
    assert result.returncode == 0 and not result.stderr, result.diagnostic()
    return native_rows(result.stdout)
