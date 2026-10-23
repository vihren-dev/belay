set_option doc.verso true

/-! The three counters of a SQLite connection that {lit}`changes()`, {lit}`total_changes()` and
{lit}`last_insert_rowid()` read (ADR 0024, D1 to D3): what a connection holds between two
statements ({lit}`Counters`), and what one statement does to them
({lit}`Counts`). A counter can be unknown, for a connection that the model
did not see start. -/

namespace Belay.Sqlite.Model

/-- The counters of a connection: SQLite's {lit}`db->nChange`, {lit}`db->nTotalChange` and
{lit}`db->lastRowid`. Each is known or unknown. For example,
{lit}`Counters.newConnection` is a connection that has run no statement, and
{lean}`({} : Counters)` knows none of the three. Use the default, with no counter known, when
the run does not start on a new connection. -/
structure Counters where
  /-- The value of {lit}`changes()`: the rows that the last write changed. -/
  changes : Option Nat := none
  /-- The value of {lit}`total_changes()`: the rows that all writes of the connection changed,
  with the rows of trigger programs and foreign-key actions. -/
  totalChanges : Option Nat := none
  /-- The value of {lit}`last_insert_rowid()`: the rowid of the last row inserted into a table
  with a rowid. -/
  lastInsertRowid : Option Int := none
  deriving DecidableEq, Repr

/-- The counters of a connection that has run no statement: SQLite starts each at 0. -/
def Counters.newConnection : Counters := { changes := some 0, totalChanges := some 0, lastInsertRowid := some 0 }

/-- What one statement does to the counters of its connection. For example, an INSERT of two
rows into a table with rowids gives
{lean}`({ changes := some 2, total := 2, lastRowid := some 5 } : Counts)` when the last row has
rowid 5. The default, with nothing set, is a statement that leaves all three counters. -/
structure Counts where
  /-- The value of {lit}`changes()` after the statement; none when the statement leaves it. -/
  changes : Option Nat := none
  /-- The rows that the statement adds to {lit}`total_changes()`: its own rows and the rows of
  its completed trigger programs and foreign-key actions. -/
  total : Nat := 0
  /-- The value of {lit}`last_insert_rowid()` after the statement; none when the statement
  leaves it. -/
  lastRowid : Option Int := none
  deriving DecidableEq, Repr

/-- The counters after a statement with the counts: {lit}`changes` and the last rowid take the
statement's value when it has one; the total adds the statement's rows, and stays unknown when it
was unknown. -/
def Counters.apply (counters : Counters) (counts : Counts) : Counters :=
  { changes := counts.changes.or counters.changes,
    totalChanges := counters.totalChanges.map (· + counts.total),
    lastInsertRowid := counts.lastRowid.or counters.lastInsertRowid }

/-- For every counters, applying the counts of a statement that leaves the counters gives the
same counters. Proof sketch: the definitions. -/
@[simp] theorem Counters.apply_default (counters : Counters) : counters.apply {} = counters := by
  simp [Counters.apply, Option.or]

end Belay.Sqlite.Model
