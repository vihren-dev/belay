"""Where a statement ends in a recording that runs on after an SQL error (native record version 6).

SQLite's prepare tail does not always end at the end of a failed statement: it stops at the
token of a syntax error, and in the middle of the text for some resolution errors (for example
`CREATE TABLE t(a, a, b)`). A recorder that runs on must find the start of the next statement
without SQLite's parser, so it takes the shortest prefix that `sqlite3_complete` accepts.
"""

import ctypes as c


def complete_statement(library: c.CDLL, remaining: bytes) -> bytes:
    """The shortest prefix of `remaining` that ends with a semicolon and that `sqlite3_complete`
    accepts, or all of `remaining` when no prefix is complete. For a statement that prepares,
    this is where SQLite's prepare tail ends."""
    end = remaining.find(b";")
    while end != -1:
        if library.sqlite3_complete(remaining[:end + 1]):
            return remaining[:end + 1]
        end = remaining.find(b";", end + 1)
    return remaining
