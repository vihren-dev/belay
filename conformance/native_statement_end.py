"""Where a statement ends in a recording that runs on after an SQL error (native record version 6).

SQLite's prepare tail does not always end at the end of a failed statement: it stops at the
token of a syntax error, and in the middle of the text for some resolution errors (for example
`CREATE TABLE t(a, a, b)`). A recorder that runs on must find the start of the next statement
without SQLite's parser, so it takes the shortest prefix that `sqlite3_complete` accepts and
that has a token other than `;`. `sqlite3_complete` also accepts an empty statement, such as a
lone `;`, which SQLite's prepare skips; such a prefix belongs to the statement after it.
"""

import ctypes as c

from conformance.query_window import tokens


def complete_statement(library: c.CDLL, remaining: bytes) -> bytes:
    """The shortest prefix of `remaining` that ends with a semicolon, that `sqlite3_complete`
    accepts, and that has a token other than `;`, or all of `remaining` when no prefix is such.
    For a statement that prepares, this is where SQLite's prepare tail ends. A semicolon is one
    byte in UTF-8 and never part of another character, so each prefix decodes."""
    end = remaining.find(b";")
    while end != -1:
        prefix = remaining[:end + 1]
        if library.sqlite3_complete(prefix) and any(token.text != ";" for token in tokens(prefix.decode())):
            return prefix
        end = remaining.find(b";", end + 1)
    return remaining
