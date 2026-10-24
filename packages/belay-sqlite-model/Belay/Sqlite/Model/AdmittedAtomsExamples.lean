import Belay.Sqlite.Model.ModelLaws
import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Examples of the theorems of the Admitted atoms (ADR 0022, slice 4), each checked by the
kernel. Part 1: the conditions of {lit}`CatalogTable.supported` that this slice adds (a key that
names a column twice, the rowid alias, and the columns that a CHECK reads), each with a table that
meets it and a table that breaks it. -/

namespace Belay.Sqlite.Model.AdmittedAtomsExamples

open Belay.Sqlite.Model Resolution.Examples

/-- The table {lit}`t(a INTEGER, b TEXT)` before its keys. -/
def twoColumns : CatalogTable :=
  { columns := [{ name := name! "a", declaredType := some "INTEGER" }, { name := name! "b", declaredType := some "TEXT" }] }

/-- A generated column. -/
def generatedColumn : CatalogColumn :=
  { name := name! "g", declaredType := some "INTEGER", generated := some { expression := .literal .null, stored := false } }

/-- A CHECK that reads the column at the position. -/
def readsColumn (position : Nat) : CheckConstraint := { condition := .column position, label := "" }

-- A key may name a column twice, as SQLite accepts `PRIMARY KEY(a, a)` and `UNIQUE(a, a)`.
example : twoColumns.supported defaults.limits = true := by decide +kernel
example : { twoColumns with primaryKey := [0, 0] }.supported defaults.limits = true := by decide +kernel
example : { twoColumns with uniqueKeys := [[1, 1]] }.supported defaults.limits = true := by decide +kernel
-- A key still needs a column, and every column of the key is a column of the table.
example : { twoColumns with uniqueKeys := [[]] }.supported defaults.limits = false := by decide +kernel
example : { twoColumns with primaryKey := [0, 2] }.supported defaults.limits = false := by decide +kernel

-- The alias is the whole primary key, a column of INTEGER affinity that is not generated, in a
-- table with a rowid.
example : { twoColumns with primaryKey := [0], rowidAlias := some 0 }.supported defaults.limits = true := by
  decide +kernel
example : { twoColumns with rowidAlias := some 0 }.supported defaults.limits = false := by decide +kernel
example : { twoColumns with primaryKey := [1], rowidAlias := some 1 }.supported defaults.limits = false := by
  decide +kernel
example : { twoColumns with primaryKey := [0, 1], rowidAlias := some 0 }.supported defaults.limits = false := by
  decide +kernel
example : { twoColumns with primaryKey := [0], rowidAlias := some 0, withoutRowid := true }.supported
    defaults.limits = false := by decide +kernel
example : { twoColumns with columns := twoColumns.columns ++ [generatedColumn], primaryKey := [2], rowidAlias := some 2 }.supported
    defaults.limits = false := by decide +kernel
example : { twoColumns with primaryKey := [5], rowidAlias := some 5 }.supported defaults.limits = false := by
  decide +kernel
example : ({ columns := [], primaryKey := [0], rowidAlias := some 0 } : CatalogTable).supported defaults.limits = false := by
  decide +kernel

-- The alias condition alone refuses an alias whose column is missing.
example : ({ columns := [], primaryKey := [0], rowidAlias := some 0 } : CatalogTable).aliasSupported = false := by
  decide +kernel
example : { twoColumns with primaryKey := [5], rowidAlias := some 5 }.aliasSupported = false := by decide +kernel

-- A CHECK of the table or of a column reads only columns of the table.
example : { twoColumns with checks := [readsColumn 1] }.supported defaults.limits = true := by decide +kernel
example : { twoColumns with checks := [readsColumn 2] }.supported defaults.limits = false := by decide +kernel
example : { twoColumns with columns := [{ name := name! "a", declaredType := none, checks := [readsColumn 2] }] }.supported
    defaults.limits = false := by decide +kernel
example : { twoColumns with columns := [{ name := name! "a", declaredType := none, checks := [readsColumn 0] }] }.supported
    defaults.limits = true := by decide +kernel

end Belay.Sqlite.Model.AdmittedAtomsExamples
