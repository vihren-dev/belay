import Belay.Sqlite.Model.Queries.Select.JoinExamples
import Belay.Sqlite.Model.Queries.Evaluation.QueryRun

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.SourceListExamples
open Belay.Sqlite.Model Syntax Resolution.JoinExamples

/-- The text value of a string. -/
def text (value : String) : Value := .text value.toUTF8.toList

/-- {lit}`json_each(argument) AS alias`. -/
def each (alias : Identifier) (argument : Expr) : TableReference :=
  { table := (name! "json_each"), alias := some alias, arguments := some [argument] }

/-- The query of a resolved statement; none for any other statement and for no statement. -/
def queryOf : Option Resolved.Statement → Option Resolved.Query
  | some (.query query _) => some query
  | some (.createTable ..) | some (.createView ..) | some (.createIndex ..) | some (.createTrigger ..) | some (.addColumn ..) | some (.rewrite _) | some (.dropColumn ..) | some (.drop ..) | some (.setting ..) | some .begin | some .commit
  | some .rollback | some (.insert ..) | some (.update ..) | some (.upsert ..) | some (.insertSelect ..) | some (.delete ..)
  | some (.prepareError _) | none => none

/-- A result column of {lit}`x.c`. -/
def named (source column : Identifier) : ResultColumn :=
  .expression (qualified source column) none s!"{source.text}.{column.text}"

end Belay.Sqlite.Model.Resolution.SourceListExamples
