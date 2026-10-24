import SuccessBalanceSuccess

/-! Kernel witnesses for the corrected balance claim and both original guide defects. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open BalanceExample
set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

/-- A nonempty ledger with integer, REAL and NULL cells retained by INTEGER affinity. -/
def mixedLedger : Database := db! r"CREATE TABLE ledger (account TEXT, cents INTEGER);
  INSERT INTO ledger VALUES ('a', 10), ('a', 1.5), ('a', NULL), ('b', -4)"
example : Holds balanceGuard mixedLedger := by decide +kernel
example : (mixedLedger.run (balance (.text (bytes! "a")))).outputs.allOk = true := by decide +kernel

/-- The corrected guard also admits an empty ledger. -/
def noEntries : Database := db! r"CREATE TABLE ledger (account TEXT, cents INTEGER)"
example : Holds balanceGuard noEntries := by decide +kernel
example : Holds (balance .null) noEntries := by decide +kernel

/-- The original guard checks only the range and total row count. -/
def originalGuard : Script := sql r"SELECT 1 WHERE
  NOT EXISTS (SELECT 1 FROM ledger WHERE cents NOT BETWEEN -1000000000000 AND 1000000000000)
  AND (SELECT count(*) FROM ledger) < 1000000"

/-- A missing account column passes the original guard but prevents SUM from resolving. -/
def missingAccount : Database := db! r"CREATE TABLE ledger (cents INTEGER)"
example : Holds originalGuard missingAccount ∧ Fails (balance .null) missingAccount := by decide +kernel
example : ¬ Holds balanceGuard missingAccount := by decide +kernel

/-- Ten text values pass the text-affinity range check, then overflow integer SUM. -/
def textOverflow : Database := db! r"CREATE TABLE ledger (account TEXT, cents TEXT);
  INSERT INTO ledger VALUES ('a', '0999999999999999999'), ('a', '0999999999999999999'),
    ('a', '0999999999999999999'), ('a', '0999999999999999999'), ('a', '0999999999999999999'),
    ('a', '0999999999999999999'), ('a', '0999999999999999999'), ('a', '0999999999999999999'),
    ('a', '0999999999999999999'), ('a', '0999999999999999999')"
example : Holds originalGuard textOverflow ∧ Fails (balance (.text (bytes! "a"))) textOverflow := by decide +kernel
example : ¬ Holds balanceGuard textOverflow := by decide +kernel

example : ¬ Holds balanceGuard Database.empty := by decide +kernel
example : let db := db! r"CREATE TABLE ledger (account TEXT)"; ¬ Holds balanceGuard db := by decide +kernel
example : let db := db! r"CREATE TABLE ledger (account TEXT, cents INTEGER);
    CREATE TABLE pragma_table_info (name TEXT)"; ¬ Holds balanceGuard db := by decide +kernel
example : let db := db! r"CREATE TABLE ledger (account TEXT, cents INTEGER);
    INSERT INTO ledger VALUES ('a', 1000000000001)"; ¬ Holds balanceGuard db := by decide +kernel

#print axioms BalanceExample.balance_ok
