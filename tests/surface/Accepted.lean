import Belay

/-! A fixture of `tests/surface_parser_test.py`: `#sql_parse` over valid SQL shows that SQLite's
grammar accepts three commands, one of them under `EXPLAIN`. -/

#sql_parse "CREATE TABLE t(a INTEGER); INSERT INTO t VALUES (1); EXPLAIN SELECT a FROM t;"
