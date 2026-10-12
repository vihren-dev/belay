"""Project-derived expected observations; deliberately independent of model execution."""

from dataclasses import dataclass

Cell = int | str | None


@dataclass(frozen=True)
class ExpectedTable:
    """Canonical declarations and rows ordered explicitly by physical rowid."""
    name: str
    columns: tuple[tuple[str, str], ...]
    rows: tuple[tuple[Cell, ...], ...]


@dataclass(frozen=True)
class Case:
    """A declared before state, SQL candidate, and independent after/error observations."""
    name: str
    before: tuple[ExpectedTable, ...]
    migration: str
    after: tuple[ExpectedTable, ...]
    lean_failure: str
    native_error: str
    kernel_proof: bool = True
    """Whether the kernel checks this case. The compiled runner classifies every case;
    the kernel evaluates resolution too slowly for a table with 2,000 columns, so that
    case stays compiled-only until a lowered profile column limit replaces it."""


def cases() -> tuple[Case, ...]:
    """Exercise success, error prefixes, missing objects, and the native column limit."""
    invoices = ExpectedTable("invoices", (("amount", "INTEGER"), ("label", "TEXT")),
                             ((-4, 7, "repeat"), (9, 7, "repeat"), (22, None, "café")))
    annotated = ExpectedTable("invoices", invoices.columns + (("note", "TEXT"),),
                              tuple(row + (None,) for row in invoices.rows))
    audit = ExpectedTable("audit", (("message", "TEXT"),), ())
    full = ExpectedTable("full", tuple((f"c{i}", "TEXT") for i in range(2000)), ())
    return (
        Case("add_then_create", (invoices,),
             "ALTER TABLE invoices ADD note TEXT; CREATE TABLE audit(message TEXT);",
             (annotated, audit), "none", ""),
        Case("retained_add_prefix", (invoices,),
             "ALTER TABLE invoices ADD note TEXT; CREATE TABLE invoices(other TEXT); "
             "CREATE TABLE unreached(value BLOB);", (annotated,),
             'some (1, .prepare (.tableExists "invoices"))', "table invoices already exists"),
        Case("retained_create_prefix", (invoices,),
             "CREATE TABLE audit(message TEXT); ALTER TABLE invoices ADD amount INTEGER;",
             (invoices, audit), 'some (1, .prepare (.duplicateColumn "amount"))',
             "duplicate column name: amount"),
        Case("missing_table_prefix", (invoices,),
             "CREATE TABLE audit(message TEXT); ALTER TABLE absent ADD note TEXT;",
             (invoices, audit), 'some (1, .prepare (.noSuchTable "absent"))', "no such table: absent"),
        Case("limit_before_duplicate", (full,), "ALTER TABLE full ADD c0 TEXT;", (full,),
             'some (0, .prepare (.tooManyColumns "full"))', "too many columns on sqlite_altertab_full",
             kernel_proof=False),
    )


def quoted(name: str) -> str:
    """Keep fixture identifiers inert in independently executed native SQL."""
    return '"' + name.replace('"', '""') + '"'


def schema_sql(tables: tuple[ExpectedTable, ...]) -> str:
    """Declare independent expected schemas as actual SQLite input."""
    return "\n".join(f"CREATE TABLE {quoted(table.name)}(" +
                     ",".join(f"{quoted(name)} {kind}" for name, kind in table.columns) + ");"
                     for table in tables)


def literal(value: Cell) -> str:
    """Encode only the integer/text/NULL cells represented by these derived cases."""
    if value is None:
        return "NULL"
    if isinstance(value, int):
        return str(value)
    return "'" + value.replace("'", "''") + "'"


def inserts_sql(tables: tuple[ExpectedTable, ...]) -> str:
    """Set real physical rowids explicitly; duplicate application values stay distinct."""
    return "\n".join(
        f"INSERT INTO {quoted(table.name)}(rowid," +
        ",".join(quoted(name) for name, _ in table.columns) + ") VALUES(" +
        ",".join(literal(cell) for cell in row) + ");"
        for table in tables for row in table.rows)
