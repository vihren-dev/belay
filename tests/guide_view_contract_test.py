"""Native counterexamples behind the guide's explicit physical-table premises.

These replay the known gaps in the earlier uniqueEmail_ok and balance_ok guards.
They test the guide contracts against the pinned oracle; they make no claim that
views are supported by the current model.
"""

from pathlib import Path

import pytest

from conformance.native_connection import Connection, NativeError, library_path, load_library

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_native("sqlite3")]


def test_email_sql_guard_can_hold_for_an_unindexable_view(tmp_path: Path) -> None:
    """SuccessUniqueEmail's SQL guard and free index name need its separate table premise."""
    connection = Connection(load_library(library_path()), tmp_path / "email.db")
    try:
        connection.execute_script("CREATE VIEW customers AS SELECT 'a@x' AS email;")
        guard = ("SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM customers "
                 "GROUP BY email COLLATE NOCASE HAVING count(*) > 1)")
        assert connection.query(guard) == [((1, 1),)]
        assert connection.query("SELECT count(*) FROM sqlite_schema WHERE name='customers_email'") == [((1, 0),)]
        with pytest.raises(NativeError, match="views may not be indexed") as failure:
            connection.query("CREATE UNIQUE INDEX customers_email ON customers(email COLLATE NOCASE)")
        assert (failure.value.code, failure.value.phase) == (1, "prepare")
    finally:
        connection.close()


def test_balance_sql_guard_can_hold_before_a_view_account_overflows(tmp_path: Path) -> None:
    """SuccessBalance's complete SQL guard cannot exclude a fallible view account expression."""
    connection = Connection(load_library(library_path()), tmp_path / "balance.db")
    try:
        connection.execute_script("CREATE TABLE t(cents INTEGER); INSERT INTO t VALUES(1);"
            "CREATE VIEW ledger AS SELECT abs(-9223372036854775808) AS account,cents FROM t;")
        guard = ("SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM ledger "
                 "WHERE cents NOT BETWEEN -1000000000000 AND 1000000000000) "
                 "AND (SELECT count(*) FROM ledger) < 1000000 "
                 "AND EXISTS (SELECT 1 FROM pragma_table_info('ledger') WHERE name='account') "
                 "AND EXISTS (SELECT 1 FROM pragma_table_info('ledger') WHERE name='cents' AND type='INTEGER')")
        assert connection.query(guard) == [((1, 1),)]
        with pytest.raises(NativeError, match="integer overflow") as failure:
            connection.query("SELECT sum(cents) FROM ledger WHERE account=1")
        assert (failure.value.code, failure.value.phase) == (1, "step")
    finally:
        connection.close()
