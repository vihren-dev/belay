import Belay

/-! A fixture of `tests/surface_parser_test.py`: `#sql_parse` over SQL with a grammar error
shows the error at `FORM`, line 6, column 21. -/

#sql_parse "SELECT * FORM t;"
