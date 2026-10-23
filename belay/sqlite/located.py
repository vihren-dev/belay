"""Statement syntax in the model's JSON transport, with its byte range in the SQL text.

The text package's translation program (`conformance.sql_text`) gives each statement's value
and range. The harness reads the start of a statement in a prediction and the start and end
of each native statement's text.
"""

from dataclasses import dataclass
from typing import TypeAlias

Json: TypeAlias = None | bool | int | str | list["Json"] | dict[str, "Json"]


@dataclass(frozen=True)
class Located:
    """One statement's syntax value and its half-open UTF-8 byte range."""

    value: Json
    start: int
    end: int
