import Belay.Sqlite.Model

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- A certificate for a read of one table: the position of the table, the width of the columns that the
read uses (it uses only columns below the width), and the resolved filter and scalar result columns. For
example, the read of the {lit}`id` column of the rows with {lit}`name = ?1` in a table at position 0, with the
columns {lit}`id, name` at positions 0 and 1, has width 2. -/
structure ReadCertificate where
  /-- The position of the table in the database. -/
  position : Nat
  /-- The read uses only the columns below this number. -/
  width : Nat
  /-- The condition of the read, when it has one. -/
  filter : Option Resolved.Expr
  /-- The result columns of the read. -/
  columns : List Resolved.Output
deriving DecidableEq

/-- The resolved query that a certificate describes, with the given result names: the simple query that
reads the table at the position, keeps the rows where the filter is true, and returns the columns. -/
def ReadCertificate.query (certificate : ReadCertificate) (names : List String) : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first certificate.position] certificate.filter certificate.columns names

/-- The resolved statement that a certificate describes: the query of the certificate with no
subqueries. -/
def ReadCertificate.statement (certificate : ReadCertificate) (names : List String) : Resolved.Statement :=
  .query (certificate.query names) []

/-- A valid certificate. In plain words, it requires three facts:
* The filter, when there is one, reads only columns below the width
  ({name}`Resolved.Expr.readsBelow`).
* Every result column is a scalar expression that reads only columns below the width. An aggregate column
  never does ({name}`Resolved.Output.readsBelow`).
* Every expression of the filter and of the columns is calm ({name}`Resolved.Expr.Calm`): it calls no
  function that can fail and reads no clock and no counter. -/
structure ReadCertificate.Valid (certificate : ReadCertificate) : Prop where
  /-- The filter reads only columns below the width. -/
  filterBelow : ∀ condition ∈ certificate.filter, condition.readsBelow certificate.width = true
  /-- The result columns read only columns below the width. -/
  columnsBelow : ∀ column ∈ certificate.columns, column.readsBelow certificate.width = true
  /-- The filter and the scalar result columns are calm. -/
  calm : ∀ expression ∈ certificate.filter.toList ++ certificate.columns.flatMap Resolved.Output.scalars,
    expression.Calm

/-- For every valid certificate and result names, the statement of the certificate is calm
({name}`Resolved.Statement.Calm`). Proof sketch: a column that reads below a width is scalar, so it has no
operands ({name}`Resolved.Output.operands_of_readsBelow`), and a one-table read with calm parts is calm
({name}`Resolved.Statement.simpleTable_calm`). -/
theorem ReadCertificate.Valid.statement_calm {certificate : ReadCertificate} (valid : certificate.Valid)
    (names : List String) : (certificate.statement names).Calm :=
  Resolved.Statement.simpleTable_calm certificate.position certificate.filter certificate.columns names valid.calm
    fun column member => Resolved.Output.operands_of_readsBelow (valid.columnsBelow column member)

/-- The certificate for the same read of the table at another position: only the position changes. In plain
words, the table that the read names can sit at another position in the catalog after a migration, for
example after the drop of an earlier table. -/
def ReadCertificate.moved (certificate : ReadCertificate) (position : Nat) : ReadCertificate :=
  { certificate with position }

/-- For every valid certificate and position, the certificate at the position is valid. In plain words,
validity does not depend on the position of the table. Proof sketch: validity looks only at the filter, the
columns and the width, which {name}`ReadCertificate.moved` keeps. -/
theorem ReadCertificate.Valid.moved {certificate : ReadCertificate} (valid : certificate.Valid)
    (position : Nat) : (certificate.moved position).Valid :=
  ⟨valid.filterBelow, valid.columnsBelow, valid.calm⟩

end Belay.Sqlite
