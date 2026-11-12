import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for the binding of parameters by name: signs, closed
values, problems of the arguments and the values in runtime messages. -/

open Belay.Sqlite

/-- A database with one table and the row 1, which most cases start from. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

/-- A table that refuses NULL and values that are not positive. -/
def checked : Database := db! r"CREATE TABLE c(x INTEGER NOT NULL CHECK (x > 0))"

/-- A closed value for the bindings by name. -/
def two : Value := 2

/-- A closed real value, which a header literal cannot write. -/
def real25 : Value := 2.5

/-- A closed NULL value. -/
def nothing : Value := .null

--! case repeated-name-needs-one-argument
/-- One argument binds every use of its name.
```sql (db := start) (v := 5)
UPDATE t SET x = :v WHERE x < :v + 1;
SELECT x FROM t;
-- 5
```
-/
def repeatedName : Unit := ()

--! case all-parameter-signs
/-- Each sign names its own parameter, and a bare question mark takes the next number.
```sql (db := start) (a := 1) (b := 2) (c := "three") (p4 := real25)
SELECT :a, @b, $c, ?;
-- 1 | 2 | three | 2.5
```
-/
def allSigns : Unit := ()

--! case sparse-numbers-bind-by-number
/-- A numbered parameter leaves the smaller numbers unused, and they stay NULL.
```sql (db := start) (p5 := 7)
SELECT ?5, ?5;
-- 7 | 7
```
-/
def sparseNumbers : Unit := ()

--! case closed-values-by-name
/-- A closed definition of a value is a binding.
```sql (db := start) (a := two) (b := real25) (c := nothing)
SELECT :a, :b, :c IS NULL;
-- 2 | 2.5 | 1
```
-/
def closedValues : Unit := ()

--! case missing-binding-is-at-the-parameter
--! error 5:7 the parameter :b has no value; add the header argument (b := value)
/-- A parameter without an argument is an error at the parameter.
```sql (db := start) (a := 1)
SELECT :a,
       :b;
-- 1
```
-/
def missingBinding : Unit := ()

--! case extra-argument-is-at-the-argument
--! error 3:30 binds no parameter
/-- An argument that no parameter needs is an error at the argument.
```sql (db := start) (a := 1) (z := 2)
SELECT :a;
-- 1
```
-/
def extraArgument : Unit := ()

--! case duplicate-argument-is-at-the-second
--! error 3:30 appears twice
/-- The same name twice is an error at the second argument.
```sql (db := start) (a := 1) (a := 2)
SELECT :a;
-- 1
```
-/
def duplicateArgument : Unit := ()

--! case reserved-name-needs-the-explicit-list
--! error 4:7 has the name db of a header option
/-- A parameter named like a header option cannot be bound by name.
```sql (db := start)
SELECT :db;
-- 1
```
-/
def reservedName : Unit := ()

--! case bound-value-decides-the-runtime-error
--! error 4:0 actual message: "CHECK constraint failed: x > 0"
/-- The message of a runtime error uses the actual bindings: zero breaks the check.
```sql (db := checked) (v := 0) +error
INSERT INTO c VALUES (:v);
-- NOT NULL constraint failed: c.x
```
-/
def zeroIsNotNull : Unit := ()

--! case bound-value-null-fails-not-null
/-- A NULL binding breaks the NOT NULL constraint.
```sql (db := checked) (v := nothing) +error
INSERT INTO c VALUES (:v);
-- NOT NULL constraint failed: c.x
```
-/
def nullIsNotNull : Unit := ()

--! case bound-value-zero-fails-check
/-- A zero binding breaks the CHECK constraint.
```sql (db := checked) (v := 0) +error
INSERT INTO c VALUES (:v);
-- CHECK constraint failed: x > 0
```
-/
def zeroFailsCheck : Unit := ()

--! case two-signs-with-one-name-need-the-explicit-list
--! error 5:11 both give the Lean name x
/-- The parameters :x and @x are different parameters. A header argument cannot tell them apart,
so the block is an error that names the explicit list.
```sql (db := start) (x := 1)
SELECT :x, @x;
-- 1 | 1
```
-/
def twoSignsOneName : Unit := ()
