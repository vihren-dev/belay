import Belay

/-! A fixture of `tests/surface_guide_test.py`: each wrong parameter of `sql r"..."`
(`Belay/Sqlite/SqlParameters.lean`, `Belay/Sqlite/SqlTerm.lean`) and each parameter of `db!`
(`Belay/Sqlite/DbBang.lean`) is an error at the parameter in the SQL text. The test reads the
line and column (from 0) of each error. -/

open Belay.Sqlite

structure NoValue where

def unknownVariable : Script := sql r"SELECT $nosuch"
def noCoercion (n : NoValue) : Script := sql r"SELECT $n"
def notIdentifier : Script := sql r"SELECT $a::b"
def notIdentifierCall : Script := sql r"SELECT $a(x)"
def colonAndAt := sql r"SELECT :id, @id"
def colonAndDollar (id : Value) := sql r"SELECT :id; SELECT $id"
def variableAndNumber (x : Value) := sql r"SELECT $x, ?1"
def nameAndNumber := sql r"SELECT :a, ?1"
def inDatabase : Database := db! r"CREATE TABLE t(a); INSERT INTO t VALUES (:a), (?)"
