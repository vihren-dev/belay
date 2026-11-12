import Belay.Sqlite.Model.Queries.Evaluation.QueryEval
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.QueryResolutionExamples

open Belay.Sqlite.Model Syntax

/-- A catalog with {lit}`t(Abc INTEGER, b TEXT)` at position 0. -/
def catalog : Catalog :=
  [{ name := (name! "t"), entry := .table { columns := [{ name := (name! "Abc"), declaredType := some "INTEGER" },
    { name := (name! "b"), declaredType := some "TEXT" }] } }]

/-- A {lit}`SELECT` from {lit}`t` with the given parts. -/
def select (columns : List ResultColumn) (filter : Option Expr := none) (groupBy : List Expr := [])
    (orderBy : List OrderTerm := []) (limit offset : Option Expr := none) : Syntax.Statement :=
  .select columns (some { table := (name! "t"), alias := none }) [] filter groupBy orderBy limit offset

/-- A result column written as an expression without an alias. -/
def written (value : Expr) (text : String) : ResultColumn := .expression value none text

/-- A {lit}`SELECT` without {lit}`FROM` with the given parts (ADR 0012, amendment 5, slice 6a). -/
def bare (columns : List ResultColumn) (filter : Option Expr := none) (groupBy : List Expr := []) : Syntax.Statement :=
  .select columns none [] filter groupBy [] none none

/-- The condition {lit}`1 = 0`, which is false. -/
def never : Expr := .compare .eq (.numeric "1") (.numeric "0")

end Belay.Sqlite.Model.Resolution.QueryResolutionExamples
