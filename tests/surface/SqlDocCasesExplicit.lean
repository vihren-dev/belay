import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for the explicit lists of values, for the closed
values that cannot be computed and for a missing database. -/

open Belay.Sqlite

/-- A database with one table and the row 1, which most cases start from. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

/-- One statement with one parameter, bound to 5. -/
def listOfFive : List (List Value) := [[5]]

/-- Five values for the five parameters whose names are header options. -/
def aliasLists : List (List Value) := [[1, 2, 3, 4, 5]]

/-- Two values for the parameters :x and @x. -/
def twoSigns : List (List Value) := [[1, 2]]

/-- No list of values, which does not fit a statement. -/
def noLists : List (List Value) := []

/-- An empty list of values for a statement with a parameter. -/
def shortList : List (List Value) := [[]]

/-- Two values for a statement with one parameter. -/
def longList : List (List Value) := [[1, 2]]

/-- Values for the numbers 1 to 3 where only number 3 is used. -/
def sparseList : List (List Value) := [[.null, .null, 8]]

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

