import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for its inputs: the parameters, the explicit lists
of values, the closed values and the database of a block. -/

open Belay.Sqlite

def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"
def checked : Database := db! r"CREATE TABLE c(x INTEGER NOT NULL CHECK (x > 0))"
def two : Value := 2
def real25 : Value := 2.5
def nothing : Value := .null
def listOfFive : List (List Value) := [[5]]
def aliasLists : List (List Value) := [[1, 2, 3, 4, 5]]
def twoSigns : List (List Value) := [[1, 2]]
def noLists : List (List Value) := []
def shortList : List (List Value) := [[]]
def longList : List (List Value) := [[1, 2]]
def sparseList : List (List Value) := [[.null, .null, 8]]

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

--! case explicit-list-binds-reserved-names
/-- The explicit list binds parameters whose names are header options, and a name that two signs share.
```sql (db := start) (values := aliasLists)
SELECT :db, :values, :env, :expected, :error;
-- 1 | 2 | 3 | 4 | 5
```
-/
def explicitReserved : Unit := ()

--! case explicit-list-keeps-distinct-signs
/-- The signs of a name are different parameters, and the list binds each of them.
```sql (db := start) (values := twoSigns)
SELECT :x, @x;
-- 1 | 2
```
-/
def explicitSigns : Unit := ()

--! case explicit-list-keeps-sparse-null
/-- Numbers that no parameter uses are NULL in the list.
```sql (db := start) (values := sparseList)
SELECT ?3, ?3;
-- 8 | 8
```
-/
def explicitSparse : Unit := ()

--! case explicit-list-with-named-argument-fails
--! error 3:44 cannot be used with (values := ...)
/-- The explicit list and named arguments exclude each other.
```sql (db := start) (values := listOfFive) (a := 1)
SELECT :a;
```
-/
def explicitAndNamed : Unit := ()

--! case explicit-list-needs-one-list-per-statement
--! error 3:21 has 0 lists and the SQL has 1 statements
/-- The count of the lists must equal the count of statements.
```sql (db := start) (values := noLists)
SELECT 1;
```
-/
def explicitWithoutLists : Unit := ()

--! case explicit-list-with-too-few-values
--! error 3:21 its list has 0 values
/-- A list shorter than the largest number is an error and not a NULL.
```sql (db := start) (values := shortList)
SELECT ?1;
```
-/
def explicitTooShort : Unit := ()

--! case explicit-list-with-too-many-values
--! error 3:21 its list has 2 values
/-- A list longer than the largest number is an error.
```sql (db := start) (values := longList)
SELECT ?1;
```
-/
def explicitTooLong : Unit := ()

--! case unevaluable-local-is-an-error
--! error 3:27 depends on a variable
/-- A binder of the declaration is not a closed value.
```sql (db := start) (v := n)
SELECT :v;
```
-/
def unevaluableLocal (n : Value) : Unit := (fun _ => ()) n

--! case missing-database-is-a-header-error
--! error 4:0 add (db := name) to the header
/-- A block needs its database.
```sql
SELECT 1;
-- 1
```
-/
def missingDatabase : Unit := ()

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
