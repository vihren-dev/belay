"""Report SQL refusal or parser failure with stable UTF-8 source coordinates."""

from typing import Literal

SqlStatus = Literal["UNVERIFIED", "UNSUPPORTED", "INPUT_ERROR"]


class SqlError(Exception):
    """A user-facing, non-success result with optional UTF-8 SQL source coordinates."""

    def __init__(self, status: SqlStatus, message: str, *, source: str = "",
                 start: int = 0, end: int = 0) -> None:
        super().__init__(message)
        self.status = status
        self.source = source
        self.start = start
        self.end = end

    def diagnostic(self) -> dict[str, str | int]:
        """Expose the refusal classification, message and exact SQL coordinates."""
        return {"status": self.status, "message": str(self), "source": self.source,
                "start": self.start, "end": self.end}


class ParserResourceLimit(SqlError):
    """The SQL text exceeds the parser's input or syntax-tree size limit.

    The parser did not decide whether the text is valid SQL, so the result is unverified.
    """

    def __init__(self, source: str, offset: int) -> None:
        """Report the limit at the offset where the parser stopped."""
        super().__init__("UNVERIFIED", "SQL exceeds the parser's limits of 1 MiB of input and 200,000 "
                         "syntax-tree nodes; split the SQL into smaller files", source=source, start=offset)


class NoParserForDialect(SqlError):
    """The parser library has no dialect for the profile; the profile's SQL is not parsed."""

    def __init__(self, message: str) -> None:
        """Report the profile as unsupported, with the reason and what to do in the message."""
        super().__init__("UNSUPPORTED", f"No parser for this dialect: {message}")
