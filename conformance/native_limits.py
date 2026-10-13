"""The run-time limits of a native connection, as an execution profile records them.

SQLite has run-time limits for each connection (`sqlite3_limit`). A compile-time
`SQLITE_MAX_*` option sets the highest value, and the connection can lower it.
ADR 0008 ("Execution profile") makes the profile record the value that applies,
measured with `sqlite3_limit(db, id, -1)`, so that name resolution uses the
limits of the measured connection instead of a constant.
"""

from collections.abc import Mapping

from conformance.native_connection import Connection

LIMIT_IDS: dict[str, tuple[int, str, int]] = {
    "columns": (2, "MAX_COLUMN", 2000),
    "expressionDepth": (3, "MAX_EXPR_DEPTH", 1000),
    "compoundSelect": (4, "MAX_COMPOUND_SELECT", 500),
    "functionArguments": (6, "MAX_FUNCTION_ARG", 1000),
    "variableNumber": (9, "MAX_VARIABLE_NUMBER", 32766),
    "length": (0, "MAX_LENGTH", 1000000000),
    "triggerDepth": (10, "MAX_TRIGGER_DEPTH", 1000),
}
"""Each recorded limit: its `SQLITE_LIMIT_*` id, its compile option and SQLite's
documented default. The names are the field names of Lean's `Limits`."""

MINIMUM_COLUMNS = 5
"""The lowest usable column limit: SQLite's own `sqlite_schema` table has 5 columns,
and below that SQLite cannot read the schema."""

Limits = dict[str, int]
"""One value for each name of `LIMIT_IDS`."""


def measured_limits(connection: Connection) -> Limits:
    """The limits that apply to the connection now, read without changing them."""
    library = connection.library
    return {name: library.sqlite3_limit(connection.handle, limit, -1) for name, (limit, _, _) in LIMIT_IDS.items()}


def lower_limits(connection: Connection, requested: Mapping[str, int]) -> Limits:
    """Set each requested limit, then return the measured limits.

    A request must name known limits and must not exceed the current value: SQLite
    silently caps a higher value at the compile-time maximum, so a higher request
    would record a limit that the fixture did not ask for. A column limit below
    `MINIMUM_COLUMNS` is refused, because the connection could not read its schema.
    """
    current = measured_limits(connection)
    for name, value in requested.items():
        lowest = MINIMUM_COLUMNS if name == "columns" else 0
        if name not in LIMIT_IDS or type(value) is not int or not lowest <= value <= current[name]:
            raise ValueError(f"Cannot lower the native limit {name} to {value!r}; the connection allows "
                             f"{lowest} to {current.get(name)}. Request a known limit in that range.")
        connection.library.sqlite3_limit(connection.handle, LIMIT_IDS[name][0], value)
    measured = measured_limits(connection)
    if any(measured[name] != value for name, value in requested.items()):
        raise RuntimeError(f"The native connection did not keep the requested limits: asked {dict(requested)}, "
                           f"measured {measured}. Check that the pinned SQLite library is in use, then request "
                           f"limits that the connection reports back unchanged.")
    return measured


def compile_option_limits(compile_options: tuple[str, ...]) -> Limits:
    """The limits of a profile recorded before profiles had a limits field.

    Its recorder kept every limit at the compile-time value, so the `SQLITE_MAX_*`
    options give them; an option that the build does not list has SQLite's
    documented default.
    """
    options = dict(option.split("=", 1) for option in compile_options if "=" in option)
    return {name: int(options.get(option, str(default)), 0) for name, (_, option, default) in LIMIT_IDS.items()}


def checked_limits(value: object) -> Limits:
    """Validate the limits field of a profile record: each limit once, as a natural number."""
    if (not isinstance(value, dict) or set(value) != set(LIMIT_IDS)
            or any(type(item) is not int or item < 0 for item in value.values())):
        raise ValueError(f"Invalid execution profile limits: expected {sorted(LIMIT_IDS)} as natural numbers")
    return dict(value)
