"""Project-derived expected observations; deliberately independent of model execution."""

from dataclasses import dataclass

Cell = int | str | None


@dataclass(frozen=True)
class ExpectedTable:
    """Canonical declarations and rows ordered explicitly by physical rowid, the explicit
    indexes of the table (name, key column names, uniqueness), the SQL constraints
    written after a column's type, and the primary-key columns they declare."""
    name: str
    columns: tuple[tuple[str, str], ...]
    rows: tuple[tuple[Cell, ...], ...]
    indexes: tuple[tuple[str, tuple[str, ...], bool], ...] = ()
    constraints: tuple[tuple[str, str], ...] = ()
    primary_key: tuple[str, ...] = ()


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
    the kernel evaluates resolution too slowly for a table with 2,000 columns, so the
    default-value case of the column limit stays compiled-only. The lowered-limit
    cases check the same rules in the kernel."""
    limits: tuple[tuple[str, int], ...] = ()
    """Connection limits that the recorder lowers before the schema runs."""


def cases() -> tuple[Case, ...]:
    """Exercise success, error prefixes, missing objects and the native column limit, and
    each first-scope resolution condition of ADR 0008 with a neighbor where it just does
    not apply: ASCII-only name folding, a table with an index's name, transaction
    control without a transaction, a ROLLBACK whose restored catalog the next statement
resolves against, and the column limit lowered to 5. The affinity
    of a `CHARINT` key and a `PRIMARY KEY DESC` that is not a rowid alias let the
    resolve mutants (`conformance.resolve_mutants`) change a verdict."""
    invoices = ExpectedTable("invoices", (("amount", "INTEGER"), ("label", "TEXT")),
                             ((-4, 7, "repeat"), (9, 7, "repeat"), (22, None, "café")))
    annotated = ExpectedTable("invoices", invoices.columns + (("note", "TEXT"),),
                              tuple(row + (None,) for row in invoices.rows))
    audit = ExpectedTable("audit", (("message", "TEXT"),), ())
    full = ExpectedTable("full", tuple((f"c{i}", "TEXT") for i in range(2000)), ())
    indexed = ExpectedTable("invoices", invoices.columns, invoices.rows, (("invoices_label", ("label",), False),))
    other = ExpectedTable("ínvoices", (("other", "TEXT"),), ())
    shouted = ExpectedTable("ÍNVOICES", (("other", "TEXT"),), ())
    keyed = ExpectedTable("keyed", (("k", "CHARINT"), ("v", "TEXT")), (), (("keyed_k", ("k",), True),))
    ranked = ExpectedTable("ranked", (("id", "INTEGER"), ("v", "TEXT")), (),
                           constraints=(("id", "PRIMARY KEY DESC"),), primary_key=("id",))
    narrow = ExpectedTable("narrow", tuple((f"c{i}", "TEXT") for i in range(4)), ())
    widened = ExpectedTable("narrow", narrow.columns + (("c4", "TEXT"),), ())
    lowered = (("columns", 5),)
    return (
        Case("add_then_create", (invoices,),
             "ALTER TABLE invoices ADD note TEXT; CREATE TABLE audit(message TEXT);",
             (annotated, audit), "none", ""),
        Case("retained_add_prefix", (invoices,),
             "ALTER TABLE invoices ADD note TEXT; CREATE TABLE invoices(other TEXT); "
             "CREATE TABLE unreached(value BLOB);", (annotated,),
             'some (1, .prepare (.tableExists (name! "invoices")))', "table invoices already exists"),
        Case("retained_create_prefix", (invoices,),
             "CREATE TABLE audit(message TEXT); ALTER TABLE invoices ADD amount INTEGER;",
             (invoices, audit), 'some (1, .prepare (.expression (.duplicateColumn (name! "amount"))))',
             "duplicate column name: amount"),
        Case("missing_table_prefix", (invoices,),
             "CREATE TABLE audit(message TEXT); ALTER TABLE absent ADD note TEXT;",
             (invoices, audit), 'some (1, .prepare (.noSuchTable (name! "absent")))', "no such table: absent"),
        Case("limit_before_duplicate", (full,), "ALTER TABLE full ADD c0 TEXT;", (full,),
             'some (0, .prepare (.expression (.tooManyColumns (name! "full"))))', "too many columns on sqlite_altertab_full",
             kernel_proof=False),
        Case("create_folded_name", (invoices,), "CREATE TABLE INVOICES(other TEXT);", (invoices,),
             'some (0, .prepare (.tableExists (name! "INVOICES")))', "table INVOICES already exists"),
        Case("create_non_ascii_name", (invoices, other), "CREATE TABLE ÍNVOICES(other TEXT);",
             (invoices, other, shouted), "none", ""),
        Case("charint_key", (keyed,), "INSERT INTO keyed(k, v) VALUES(1, 'a');",
             (ExpectedTable("keyed", keyed.columns, ((1, 1, "a"),), keyed.indexes),), "none", ""),
        Case("integer_key_desc", (ranked,), "INSERT INTO ranked(id, v) VALUES(7, 'a');",
             (ExpectedTable("ranked", ranked.columns, ((1, 7, "a"),), constraints=ranked.constraints,
                            primary_key=ranked.primary_key),), "none", ""),
        Case("table_named_like_index", (indexed,), "CREATE TABLE invoices_label(other TEXT);", (indexed,),
             'some (0, .prepare (.indexNameUsed (name! "invoices_label")))', "there is already an index named invoices_label"),
        Case("commit_without_transaction", (invoices,), "COMMIT;", (invoices,),
             "some (0, .noActiveTransaction)", "cannot commit - no transaction is active"),
        Case("rollback_without_transaction", (invoices,), "ROLLBACK;", (invoices,),
             "some (0, .noActiveTransaction)", "cannot rollback - no transaction is active"),
        Case("begin_rollback", (invoices,), "BEGIN; ALTER TABLE invoices ADD note TEXT; ROLLBACK;", (invoices,),
             "none", ""),
        Case("rollback_then_add", (invoices,),
             "BEGIN; ALTER TABLE invoices ADD note TEXT; ROLLBACK; ALTER TABLE invoices ADD note TEXT;",
             (annotated,), "none", ""),
        Case("lowered_limit_reached", (narrow,), "ALTER TABLE narrow ADD c4 TEXT;", (widened,), "none", "",
             limits=lowered),
        Case("lowered_limit_exceeded", (widened,), "ALTER TABLE narrow ADD c5 TEXT;", (widened,),
             'some (0, .prepare (.expression (.tooManyColumns (name! "narrow"))))', "too many columns on sqlite_altertab_narrow",
             limits=lowered),
        Case("lowered_limit_before_duplicate", (widened,), "ALTER TABLE narrow ADD c0 TEXT;", (widened,),
             'some (0, .prepare (.expression (.tooManyColumns (name! "narrow"))))', "too many columns on sqlite_altertab_narrow",
             limits=lowered),
    )


def quoted(name: str) -> str:
    """Keep fixture identifiers inert in independently executed native SQL."""
    return '"' + name.replace('"', '""') + '"'


def schema_sql(tables: tuple[ExpectedTable, ...]) -> str:
    """Declare independent expected schemas, then their indexes, as actual SQLite input."""
    return "\n".join([*(f"CREATE TABLE {quoted(table.name)}(" +
                       ",".join(f"{quoted(name)} {kind}" + "".join(f" {sql}" for column, sql in table.constraints
                                                                   if column == name)
                                for name, kind in table.columns) + ");"
                       for table in tables),
                     *(f"CREATE {'UNIQUE ' if unique else ''}INDEX {quoted(name)} ON {quoted(table.name)}(" +
                       ",".join(quoted(column) for column in columns) + ");"
                       for table in tables for name, columns, unique in table.indexes)])


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
