"""Keep proof failure distinct from unsupported semantics and invalid inputs."""

from collections.abc import Mapping
from typing import Literal

Status = Literal["VERIFIED", "VIOLATED", "UNVERIFIED", "UNSUPPORTED", "INPUT_ERROR"]


class Rejection(Exception):
    """A user-facing, non-success result with optional UTF-8 SQL source coordinates."""

    def __init__(self, status: Status, message: str, *, source: str = "",
                 start: int = 0, end: int = 0, details: Mapping[str, object] | None = None) -> None:
        super().__init__(message)
        self.status = status
        self.source = source
        self.start = start
        self.end = end
        self.details = dict(details or {})
        """Further report fields of the command, such as `compiled_modules` (ADR 0010)."""

    def diagnostic(self) -> dict[str, object]:
        """Expose stable machine-readable coordinates without claiming a counterexample."""
        return {**self.details, "status": self.status, "message": str(self), "source": self.source,
                "start": self.start, "end": self.end}
