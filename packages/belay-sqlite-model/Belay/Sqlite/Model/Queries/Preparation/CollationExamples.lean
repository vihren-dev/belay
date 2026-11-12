import Belay.Sqlite.Model.Queries.Select.JoinExamples
import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CollationExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A TEXT column with a COLLATE constraint. -/
def collated (name : Identifier) (collation : Identifier) : ColumnDefinition :=
  { name, declaredType := some "TEXT", constraints := [.collate collation] }

/-- {lit}`c(n TEXT COLLATE NOCASE, r TEXT COLLATE RTRIM, b TEXT)`. -/
def tableC : Syntax.Statement :=
  .createTable (name! "c") [collated (name! "n") (name! "NOCASE"), collated (name! "r") (name! "rtrim"), column (name! "b")] []

/-- {lit}`w(n TEXT, b TEXT)`, without collations. -/
def tableW : Syntax.Statement := .createTable (name! "w") [column (name! "n"), column (name! "b")] []

/-- {lit}`u(k TEXT COLLATE NOCASE UNIQUE)`. -/
def tableU : Syntax.Statement :=
  .createTable (name! "u") [{ name := name! "k", declaredType := some "TEXT", constraints := [.collate (name! "nocase"), .unique] }] []

#guard (PrepareError.expression (.noSuchCollation (name! "foo"))).message == "no such collation sequence: foo"

end Belay.Sqlite.Model.Resolution.CollationExamples
