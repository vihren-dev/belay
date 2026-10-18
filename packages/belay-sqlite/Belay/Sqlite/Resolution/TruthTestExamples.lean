import Belay.Sqlite.Resolution.QueryResolutionExamples

set_option doc.verso true

/-! Checked examples of the keywords TRUE and FALSE and of SQLite's truth test
{lit}`x IS [NOT] TRUE|FALSE` in a query without {lit}`FROM` (ADR 0013, steps 1 and 4). Each
value was checked on native SQLite 3.51.0. -/

namespace Belay.Sqlite.Resolution.TruthTestExamples

open Belay.Sqlite Syntax Resolution.Examples Resolution.QueryResolutionExamples

-- An unquoted TRUE or FALSE that names no column is 1 or 0; in brackets or backticks it is
-- only a name, so `no such column` (checked natively).
#guard bareRows (bare [written (.identifier "TRUE" .none) "TRUE", written (.identifier "false" .none) "false"]) ==
  some [[.integer 1, .integer 0]]
#guard errorOf (bare [written (.identifier "TRUE" .bracket) "[TRUE]"]) == some (.expression (.noSuchColumn "TRUE"))
#guard errorOf (bare [written (.identifier "false" .backtick) "`false`"]) == some (.expression (.noSuchColumn "false"))
-- `x IS [NOT] TRUE|FALSE` is SQLite's truth test of any operand (checked natively): `2 IS TRUE`,
-- `(1 + 1) IS TRUE` and `CAST(2 AS INTEGER) IS TRUE` are 1, `2 IS 1` is 0, and NULL is neither
-- TRUE nor FALSE.
#guard bareRows (bare [written (.compare .is (.compare .lt (.numeric "1") (.numeric "2")) (.identifier "TRUE" .none))
    "(1 < 2) IS TRUE", written (.compare .isNot (.compare .gt (.numeric "1") (.numeric "2"))
    (.identifier "TRUE" .none)) "(1 > 2) IS NOT TRUE"]) == some [[.integer 1, .integer 1]]
#guard bareRows (bare [written (.compare .is (.numeric "2") (.identifier "TRUE" .none)) "2 IS TRUE",
    written (.compare .is (.arithmetic .add (.numeric "1") (.numeric "1")) (.identifier "TRUE" .none)) "(1 + 1) IS TRUE",
    written (.compare .is (.cast (.numeric "2") "INTEGER") (.identifier "TRUE" .none)) "CAST(2 AS INTEGER) IS TRUE",
    written (.compare .is (.numeric "2") (.numeric "1")) "2 IS 1"]) ==
  some [[.integer 1, .integer 1, .integer 1, .integer 0]]
#guard bareRows (bare [written (.compare .is .null (.identifier "TRUE" .none)) "NULL IS TRUE",
    written (.compare .is .null (.identifier "FALSE" .none)) "NULL IS FALSE",
    written (.compare .isNot .null (.identifier "FALSE" .none)) "NULL IS NOT FALSE",
    written (.compare .isNot (.numeric "0") (.identifier "FALSE" .none)) "0 IS NOT FALSE"]) ==
  some [[.integer 0, .integer 0, .integer 1, .integer 0]]
-- A TEXT condition is true when its numeric prefix is not zero.
#guard bareRows (bare [written (.compare .is (.string "1ab".toUTF8.toList) (.identifier "TRUE" .none)) "'1ab' IS TRUE",
    written (.compare .is (.string "abc".toUTF8.toList) (.identifier "TRUE" .none)) "'abc' IS TRUE",
    written (.compare .is (.string "0.9".toUTF8.toList) (.identifier "TRUE" .none)) "'0.9' IS TRUE"]) ==
  some [[.integer 1, .integer 0, .integer 1]]

end Belay.Sqlite.Resolution.TruthTestExamples
