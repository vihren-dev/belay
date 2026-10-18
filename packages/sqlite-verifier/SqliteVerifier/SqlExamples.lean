import Belay.Sqlite.SqlProofs

set_option doc.verso true

/-! Kernel-checked finite SQL regressions complement independent native comparisons.
They exercise ordinary tables and values at catalog positions, not
application-specific policy. -/

open Belay.Sqlite

namespace SqliteVerifier.SqlExamples

/-- The retained BIGINT key and nonnullable text field for these finite checks.
BIGINT is an ordinary key column, independent of the physical rowid. -/
def columns : List CatalogColumn := [
  { name := "key", declaredType := some "BIGINT" },
  { name := "value", declaredType := some "TEXT", notNull := true }]

/-- Shared key metadata, negative physical identities and a NULL key exercise both distinct semantics. -/
def original : Table where
  shape := { columns := columns, primaryKey := [0] }
  rows := [⟨-5, [.null, .text [97]]⟩, ⟨-2, [.integer 1, .text [98]]⟩]

/-- The finite starting database contains {name}`original` only, at catalog position 0. -/
def database : Database := .ofTables [("t", original)]

/-- The nullable text field appended by the finite script, using the plain column
defaults. Existing rows receive NULL in this field. -/
def note : CatalogColumn := { name := "note", declaredType := some "TEXT" }

/-- The unique keys of the table, which execution reads from the catalog for every write:
the primary key on position 0. -/
def keys : List (List Nat) := [[0]]

/-- The file itself supplies both transaction control and literal writes. -/
def script : List Resolved.Statement := [.begin, .addColumn 0 note,
  .insert 0 [[.value (.integer 2), .value (.text [99]), .value .null]] [],
  .commit, .update 0 [(1, .literal (.text [100]))] (some (.compare .eq (some .integer) (.column 0) (.literal (.integer 2)))) []]

/-- Return true exactly for a pending transaction; success and failure return
false. Use it to check transaction status. -/
def openTransaction : Outcome → Bool
  | .pending .. => true
  | _ => false

/-- Read a failure position/error from either a closed failure or a pending
transaction with an error. Successful and error-free pending outcomes return
{name}`Option.none`. Use it alongside {name}`openTransaction` to distinguish them. -/
def error : Outcome → Option (Nat × ExecutionError)
  | .failure position reason _ => some (position, reason)
  | .pending _ _ reason => reason
  | .success _ => none

example : LiteralData.nextRowid original.rows = -1 := by decide +kernel
example : supportedSqlFrom 0 script { database := database } = true := by decide +kernel
example : error (runSql script database) = none ∧ openTransaction (runSql script database) = false := by
  decide +kernel
example : ((runSql script database).database.table 0).map Table.rows = some [
    ⟨-5, [.null, .text [97], .null]⟩, ⟨-2, [.integer 1, .text [98], .null]⟩,
    ⟨-1, [.integer 2, .text [100], .null]⟩] := by decide +kernel

/-- The unique-key failure stops after ADD, while BEGIN remains open. -/
def rejected : List Resolved.Statement := [.begin, .addColumn 0 note,
  .insert 0 [[.value (.integer 1), .value (.text []), .value .null]] [], .rollback]

example : error (runSql rejected database) = some (2, .constraintViolation) ∧
    openTransaction (runSql rejected database) = true := by decide +kernel
example : ((runSql rejected database).database.table 0).map (fun table => table.shape.columns) = some (columns ++ [note]) ∧
    ((runSql rejected database).persistedDatabase.table 0).map (fun table => table.shape.columns) = some columns := by
  decide +kernel
example : ((runSql [.begin, .insert 0 [[.value (.integer 2), .value (.text [])]] [], .rollback] database).database.table 0) =
    some original := by decide +kernel
example : error (runSql [.commit] database) = some (0, .noActiveTransaction) := by decide +kernel
example : error (runSql [.begin, .begin] database) = some (1, .transactionAlreadyActive) := by decide +kernel
example : openTransaction (runSql [.begin] database) = true := by decide +kernel
example : error (runSql [.insert 0 [[.value (.integer 2), .value .null]] []] database) = some (0, .constraintViolation) := by
  decide +kernel
-- Two rows of one INSERT that share a key fail together, and the table is unchanged.
example : error (runSql [.insert 0 [[.value (.integer 3), .value (.text [])], [.value (.integer 3), .value (.text [])]] []] database) =
    some (0, .constraintViolation) := by decide +kernel
-- A prepare error that resolution decided stops the script at its position.
example : error (runSql [.begin, .prepareError (.noSuchTable "t")] database) =
    some (1, .prepare (.noSuchTable "t")) := by decide +kernel

-- A value that the affinity would convert is not in stored form, and random rowid
-- allocation fails the domain obligation; neither is a modeled native constraint error.
-- Nullable duplicate keys remain supported.
example : LiteralData.storedForm .text (.integer 7) = false := by decide +kernel
example : LiteralData.storedForm .numeric (.text [49, 50]) = false := by decide +kernel
example : LiteralData.storedForm .numeric
    (.text "2026-09-25 00:00:00".toUTF8.toList) = true := by decide +kernel
example : LiteralData.insertReady keys { original with rows := [⟨9223372036854775807, [.null, .text []]⟩] }
    [[.integer 2, .text []]] = false := by decide +kernel
example : LiteralData.constraints keys (LiteralData.inserted original [[.null, .text []]]) = true := by decide +kernel
example : ¬ SchemaOnly script := by simp [SchemaOnly, script]

end SqliteVerifier.SqlExamples
