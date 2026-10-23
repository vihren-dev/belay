import Belay

/-! A fixture of `tests/surface_guide_test.py`: the examples of the user guide's section
"Scripts" that need no run (`Belay/Sqlite/Script.lean`, `Belay/Sqlite/SqlTerm.lean`), and the
values of each statement (ADR 0019, D1): `sql r"..."` binds none, `Script.withValues` binds them,
`++` keeps each statement's values, and a run reads them. The file fails to elaborate when an
example does not hold. -/

open Belay.Sqlite

/-- A script of two statements: one table and one row. -/
def createInvoices : Script := sql r"CREATE TABLE invoices(id INTEGER PRIMARY KEY, amount); INSERT INTO invoices VALUES (1, 10)"

/-- A script of one query, in a raw string with a double quote. -/
def openInvoices : Script := sql r#"SELECT "id" FROM invoices WHERE amount > 0"#

-- Every statement form is in a script, in the order of the text.
example : (sql r"BEGIN; COMMIT").statements = [(.begin, []), (.commit, [])] := rfl
example : createInvoices.statements.length = 2 := rfl
example : Script.empty.statements = [] := rfl

-- `p ++ q` is the statements of `p`, then those of `q`; `Script.empty` is the unit.
example : (createInvoices ++ openInvoices).statements.length = 3 := rfl
example (p : Script) : Script.empty ++ p = p := Script.empty_append p
example (p : Script) : p ++ Script.empty = p := Script.append_empty p
example (p q r : Script) : p ++ q ++ r = p ++ (q ++ r) := Script.append_assoc p q r

-- `sql r"..."` gives each statement no values; `Script.withValues` gives statement i list i,
-- and the empty list past the end of the lists. `++` keeps the values of each statement.
example : (sql r"SELECT ?1; SELECT ?1").statements.map (·.2) = [[], []] := rfl
example : ((sql r"SELECT ?1; SELECT ?1").withValues [[.integer 5]]).statements.map (·.2) = [[.integer 5], []] := rfl
example : ((sql r"SELECT ?1").withValues [[.integer 5]] ++ sql r"SELECT ?1").statements.map (·.2) =
    [[.integer 5], []] := rfl
-- A run reads the values of each statement: a parameter without a value is NULL.
example : (Database.empty.run ((sql r"SELECT ?1, ?2; SELECT ?1").withValues [[.integer 7]])).outputs =
    [.rows [[.integer 7, .null]], .rows [[.null]]] := by decide +kernel
