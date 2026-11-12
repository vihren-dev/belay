import Belay.Sqlite.Model.Queries.Preparation.IndexExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.NondeterministicExamples

open Belay.Sqlite.Model Syntax

/-- The call {lit}`changes()`. -/
def changes : Expr := .call "changes" []
/-- The call {lit}`total_changes()`. -/
def totalChanges : Expr := .call "total_changes" []
/-- The call {lit}`last_insert_rowid()`. -/
def lastInsertRowid : Expr := .call "last_insert_rowid" []
/-- The call {lit}`random()`. -/
def random : Expr := .call "random" []
/-- The call {lit}`randomblob(1)`. -/
def randomblob : Expr := .call "randomblob" [.numeric "1"]

/-- The column {lit}`a` of the tables of the examples. -/
def a : Expr := .identifier (name! "a") .none
/-- A name that is no column of the tables of the examples. -/
def missing : Expr := .identifier (name! "nosuch") .none

end Belay.Sqlite.Model.Resolution.NondeterministicExamples
