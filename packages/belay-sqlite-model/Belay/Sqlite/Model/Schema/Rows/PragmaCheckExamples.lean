import Belay.Sqlite.Model.Schema.Rows.ValidityExamples
import Belay.Sqlite.Model.Shared.Execution.ScriptRun

set_option doc.verso true

namespace Belay.Sqlite.Model.PragmaCheckExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ValidityExamples

/-- The rows of a check pragma with the texts. -/
def textRows (texts : List String) : List (List Value) := texts.map fun text => [textValue text]

/-- The column of an index term. -/
def term (column : String) : OrderTerm := { expression := name column, descending := false }

/-- {lit}`CREATE TABLE t(a NOT NULL, b CHECK (b > 0), c, d INTEGER PRIMARY KEY)` and
{lit}`CREATE UNIQUE INDEX tc ON t(c)`, with three rows that no statement writes. -/
def brokenT : Database :=
  (built [.createTable (name! "t") [typed "a" none [.notNull],
      typed "b" none [.check (.compare .gt (name "b") (.numeric "0")) "b > 0"], typed "c" none,
      typed "d" (some "INTEGER") [.primaryKey false]] [],
    .createIndex (name! "tc") true (name! "t") [term "c"] none]).setRows 0
    [stored 1 [.null, .integer (-1), textValue "u", .integer 1], stored 2 [.null, .integer 5, textValue "u", .integer 2],
     stored 3 [.integer 3, .integer (-2), textValue "v", .integer 3]]

-- The database is admitted, not valid.
example : brokenT.Admitted defaults ∧ ¬brokenT.Valid defaults := by decide +kernel

-- For each row in rowid order: its NULL, its CHECK, and then its index entry when a later
-- entry has an equal key. quick_check does not check the index.
example : brokenT.checkRows false 0 none = some (textRows ["NULL value in t.a", "CHECK constraint failed in t",
    "non-unique entry in index tc", "NULL value in t.a", "CHECK constraint failed in t"]) := by decide +kernel
example : brokenT.checkRows true 0 none = some (textRows ["NULL value in t.a", "CHECK constraint failed in t",
    "NULL value in t.a", "CHECK constraint failed in t"]) := by decide +kernel

/-- {lit}`CREATE TABLE s(x INTEGER NOT NULL, y TEXT NOT NULL, z INT, q INTEGER, r REAL) STRICT`,
with two rows that no statement writes. -/
def brokenS : Database :=
  (built [.createTable (name! "s") [typed "x" (some "INTEGER") [.notNull], typed "y" (some "TEXT") [.notNull],
    typed "z" (some "INT"), typed "q" (some "INTEGER"), typed "r" (some "REAL")] [] { strict := true }]).setRows 0
    [stored 1 [.null, .integer 1, textValue "a", .real 0x4004000000000000, textValue "z"],
     stored 2 [.integer 1, textValue "x", .integer 2, .integer 3, .blob [0]]]

-- One row for each cell, in column order, with the name of the STRICT type.
example : brokenS.checkRows false 0 none = some (textRows ["NULL value in s.x", "non-TEXT value in s.y",
    "non-INT value in s.z", "non-INTEGER value in s.q", "non-REAL value in s.r", "non-REAL value in s.r"]) := by
  decide +kernel

/-- {lit}`CREATE TABLE u(k, v, f)` with the unique indexes {lit}`ui ON u(k) WHERE f > 0`,
{lit}`un ON u(v COLLATE NOCASE)` and {lit}`uk ON u(k, v)`, created in this order, and five rows
that no statement writes. -/
def brokenU : Database :=
  (built [.createTable (name! "u") [typed "k" none, typed "v" none, typed "f" none] [],
    .createIndex (name! "ui") true (name! "u") [term "k"] (some (.compare .gt (name "f") (.numeric "0"))),
    .createIndex (name! "un") true (name! "u") [{ expression := .collate (name "v") (name! "NOCASE"), descending := false }]
      none,
    .createIndex (name! "uk") true (name! "u") [term "k", term "v"] none]).setRows 0
    [stored 1 [.integer 1, textValue "A", .integer 1], stored 2 [.integer 1, textValue "a", .integer 1],
     stored 3 [.integer 1, .null, .integer 0], stored 4 [.integer 2, .null, .integer 1],
     stored 5 [.integer 2, .null, .integer 1]]

-- The indexes newest first: 'A' and 'a' are equal under NOCASE; the partial index has only
-- the rows with f > 0; a NULL makes an entry unique.
example : brokenU.checkRows false 0 none = some (textRows ["non-unique entry in index un", "non-unique entry in index ui",
    "non-unique entry in index ui"]) := by decide +kernel

-- Of three rows with an equal key, the first two fail.
example : (brokenU.setRows 0 [stored 1 [.integer 1, .null, .integer 1], stored 2 [.integer 1, .null, .integer 1],
    stored 3 [.integer 1, .null, .integer 1]]).checkRows false 0 none =
    some (textRows ["non-unique entry in index ui", "non-unique entry in index ui"]) := by decide +kernel

/-- {lit}`CREATE TABLE w(k, v, PRIMARY KEY (k)) WITHOUT ROWID`, with four rows that no statement
writes. -/
def brokenW : Database :=
  (built [.createTable (name! "w") [typed "k" none, typed "v" none] [.primaryKey [name! "k"]]
    { withoutRowid := true }]).setRows 0
    [stored 0 [.integer 1, .integer 1], stored 0 [.integer 1, .integer 2], stored 0 [.integer 1, .integer 3],
     stored 0 [.integer 2, .integer 1]]

-- A row whose key equals that of the row before it is not in key order; quick_check does not
-- check the order, and the key has no index to check.
example : brokenW.checkRows false 0 none = some (textRows ["row not in PRIMARY KEY order for w",
    "row not in PRIMARY KEY order for w"]) := by decide +kernel
example : brokenW.checkRows true 0 none = some (textRows ["ok"]) := by decide +kernel

/-- {lit}`CREATE TABLE d(k INTEGER PRIMARY KEY DESC, v UNIQUE COLLATE NOCASE, c CHECK (c > 0))
WITHOUT ROWID`, with three rows that no statement writes, in the scan order {lit}`k` = 3, 2, 1. -/
def brokenD : Database :=
  (built [.createTable (name! "d") [typed "k" (some "INTEGER") [.primaryKey true],
      typed "v" none [.unique, .collate (name! "NOCASE")], typed "c" none [.check (.compare .gt (name "c") (.numeric "0")) "c > 0"]]
    [] { withoutRowid := true }]).setRows 0
    [stored 0 [.integer 3, textValue "a", .integer 1], stored 0 [.integer 2, textValue "A", .integer (-1)],
     stored 0 [.integer 1, textValue "b", .integer 1]]

-- The index of the UNIQUE constraint orders the equal entries by k in ascending order, so the
-- entry of the row with k = 2, the second row in the scan, has an equal entry after it.
example : brokenD.checkRows false 0 none = some (textRows ["CHECK constraint failed in d",
    "non-unique entry in index sqlite_autoindex_d_2"]) := by decide +kernel
/-- {lit}`CREATE TABLE d(k INTEGER PRIMARY KEY DESC, v COLLATE NOCASE, c CHECK (c > 0)) WITHOUT
ROWID` and {lit}`CREATE UNIQUE INDEX dv ON d(v)`, with two rows that no statement writes. -/
def declaredD : Database :=
  (built [.createTable (name! "d") [typed "k" (some "INTEGER") [.primaryKey true],
      typed "v" none [.collate (name! "NOCASE")], typed "c" none [.check (.compare .gt (name "c") (.numeric "0")) "c > 0"]]
    [] { withoutRowid := true }, .createIndex (name! "dv") true (name! "d") [term "v"] none]).setRows 0
    [stored 0 [.integer 3, textValue "A", .integer 1], stored 0 [.integer 2, textValue "a", .integer (-1)]]

-- A declared unique index orders the equal entries in scan order, so the first row fails.
example : declaredD.checkRows false 0 none = some (textRows ["non-unique entry in index dv",
    "CHECK constraint failed in d"]) := by decide +kernel

/-- {lit}`CREATE TABLE n(a NOT NULL UNIQUE)`, with two NULL rows that no statement writes. -/
def brokenN : Database :=
  (built [.createTable (name! "n") [typed "a" none [.notNull, .unique]] []]).setRows 0 [stored 1 [.null], stored 2 [.null]]

-- A NULL in a NOT NULL key column does not make the entry unique.
example : brokenN.checkRows false 0 none = some (textRows ["NULL value in n.a",
    "non-unique entry in index sqlite_autoindex_n_1", "NULL value in n.a"]) := by decide +kernel

/-- {lit}`CREATE TABLE p(a NOT NULL)` and {lit}`CREATE TABLE q(a NOT NULL)`, with a NULL row in
{lit}`p` that no statement writes. -/
def brokenP : Database :=
  (built [.createTable (name! "p") [typed "a" none [.notNull]] [],
    .createTable (name! "q") [typed "a" none [.notNull]] []]).setRows 0 [stored 1 [.null]]

/-- The names of the indexes that {lit}`integrity_check` checks for the first table that the
script creates, in their order. -/
def checkedNames (script : List Syntax.Statement) : List Identifier :=
  let database := built script
  match database.catalog.tableAt 0 with
  | some table => (database.catalog.checkedIndexes 0 (name! "t") table).map (·.name)
  | none => []

-- The constraint indexes are numbered in text order, and a key that repeats gets no index.
example : checkedNames [.createTable (name! "t") [typed "a" none [.unique], typed "b" none [.primaryKey false],
    typed "c" none] [.unique [name! "c"], .unique [name! "a"]]] =
    [name! "sqlite_autoindex_t_3", name! "sqlite_autoindex_t_2", name! "sqlite_autoindex_t_1"] := by decide +kernel
-- An index of a REPLACE constraint comes last.
example : checkedNames [.createTable (name! "t") [typed "a" none [.unique], typed "b" none [.unique (some .replace)]] []] =
    [name! "sqlite_autoindex_t_1", name! "sqlite_autoindex_t_2"] := by decide +kernel

end Belay.Sqlite.Model.PragmaCheckExamples
