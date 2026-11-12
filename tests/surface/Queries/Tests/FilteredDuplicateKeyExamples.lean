import GlobalSignupInvariant

/-! A fixture module of `tests/surface_assertion_examples_test.py`: concrete databases for the filtered duplicate-key
query of the global signup invariant (ADR 0017, S6). The query `SELECT 1 WHERE NOT EXISTS (SELECT email FROM accounts
WHERE deleted_at IS NULL GROUP BY email [COLLATE NOCASE] HAVING count(*) > 1)` holds when no two live accounts have
emails in one group. The kernel states the result for each database. The same text is logged for native SQLite, which
gives the same result (`tests/surface_assertion_examples_test.py`). -/

set_option doc.verso true
set_option maxRecDepth 200000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The guide invariant with the grouping under the collation NOCASE. -/
def oneLiveNocase : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT email FROM accounts WHERE deleted_at IS NULL GROUP BY email COLLATE NOCASE HAVING count(*) > 1)"

/-- Two live accounts with different emails. -/
def noLiveDuplicate : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT, deleted_at TEXT);
  INSERT INTO accounts (email) VALUES ('a@x'), ('b@x');"

/-- Two live accounts with the same email. -/
def liveDuplicate : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT, deleted_at TEXT);
  INSERT INTO accounts (email) VALUES ('a@x'), ('a@x');"

/-- A live and a deleted account with the same email: the deleted one is not counted. -/
def deletedDuplicate : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT, deleted_at TEXT);
  INSERT INTO accounts (email) VALUES ('a@x');
  INSERT INTO accounts (email, deleted_at) VALUES ('a@x', '2026-10-01');"

/-- Two live accounts without an email: GROUP BY puts two NULL keys in one group, unlike a UNIQUE index. -/
def nullKeys : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT, deleted_at TEXT);
  INSERT INTO accounts (email) VALUES (NULL), (NULL);"

/-- Two live accounts whose emails are equal only under NOCASE. -/
def nocaseDuplicate : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT, deleted_at TEXT);
  INSERT INTO accounts (email) VALUES ('A@x'), ('a@x');"

/-- The results of the query on the five databases. Plain words: no live duplicate and a deleted duplicate hold; a live
duplicate and two NULL keys do not hold; the emails that differ only in case hold under BINARY and do not hold under
NOCASE. -/
theorem filtered_duplicate_cases :
    Holds oneLive noLiveDuplicate ∧ ¬ Holds oneLive liveDuplicate ∧ Holds oneLive deletedDuplicate ∧
    ¬ Holds oneLive nullKeys ∧ Holds oneLive nocaseDuplicate ∧ ¬ Holds oneLiveNocase nocaseDuplicate := by
  decide +kernel

#print axioms filtered_duplicate_cases

open Lean Elab Meta in
/-- The SQL of each database and query, with the result that the model gives, for the native check: one JSON line for
each case. The examples above check the same results in the kernel. -/
elab "report_filtered_duplicates" : command => Command.liftTermElabM do
  let cases : List (String × Name × Name × Bool) := [
    ("noLiveDuplicate", ``noLiveDuplicate, ``oneLive, decide (Holds oneLive noLiveDuplicate)),
    ("liveDuplicate", ``liveDuplicate, ``oneLive, decide (Holds oneLive liveDuplicate)),
    ("deletedDuplicate", ``deletedDuplicate, ``oneLive, decide (Holds oneLive deletedDuplicate)),
    ("nullKeys", ``nullKeys, ``oneLive, decide (Holds oneLive nullKeys)),
    ("nocaseBinary", ``nocaseDuplicate, ``oneLive, decide (Holds oneLive nocaseDuplicate)),
    ("nocaseNocase", ``nocaseDuplicate, ``oneLiveNocase, decide (Holds oneLiveNocase nocaseDuplicate))]
  for (label, database, query, holds) in cases do
    let (_, setup) ← Replay.construction (mkConst database)
    let script ← Replay.scriptText (mkConst query)
    logInfo m!"FILTERED-DUPLICATES:{(Json.mkObj [("name", toJson label), ("setup", toJson setup),
      ("query", toJson script.text), ("holds", toJson holds)]).compress}"

report_filtered_duplicates

end AssertionExamples
