import SelectDuplicateKeySupport

/-! A fixture of `tests/surface_claims_test.py`: the query form `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t GROUP BY k
HAVING count(*) > 1)` over every database (ADR 0017, S4), through the phase rules of ADR 0027
(`SelectDuplicateKeySupport.lean`). Each claim is about
every database; each claim has instances on databases, where `decide +kernel` checks that its two sides agree, so that
no claim is vacuous. The instances include a column with the collation `NOCASE` (two keys that differ only in case are
one group) and two NULL keys (NULL keys are one group, unlike a `UNIQUE` index). -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A table `users` whose `email` has the collation `NOCASE`, with three different addresses. -/
def distinctUsers : Database := db! r"
  CREATE TABLE users (id INTEGER PRIMARY KEY, email TEXT COLLATE NOCASE);
  INSERT INTO users (id, email) VALUES (1, 'a@x.org'), (2, 'b@x.org'), (3, 'c@x.org');"

/-- The same table, where the addresses of rows 1 and 2 differ only in case. -/
def caseUsers : Database := db! r"
  CREATE TABLE users (id INTEGER PRIMARY KEY, email TEXT COLLATE NOCASE);
  INSERT INTO users (id, email) VALUES (1, 'a@x.org'), (2, 'A@X.ORG'), (3, 'c@x.org');"

/-- The same table, where rows 1 and 2 have no address. -/
def nullUsers : Database := db! r"
  CREATE TABLE users (id INTEGER PRIMARY KEY, email TEXT COLLATE NOCASE);
  INSERT INTO users (id, email) VALUES (1, NULL), (2, NULL), (3, 'c@x.org');"

/-- The catalog position and the table of `users` in `distinctUsers`. -/
def distinctTable : Nat × CatalogTable :=
  (distinctUsers.raw.catalog.findTable (name! "users")).get (by decide +kernel)

/-- The catalog position and the table of `users` in `caseUsers`. -/
def caseTable : Nat × CatalogTable := (caseUsers.raw.catalog.findTable (name! "users")).get (by decide +kernel)

/-- The catalog position and the table of `users` in `nullUsers`. -/
def nullTable : Nat × CatalogTable := (nullUsers.raw.catalog.findTable (name! "users")).get (by decide +kernel)

example : distinctUsers.raw.catalog.findTable (name! "users") = some distinctTable := by decide +kernel
example : caseUsers.raw.catalog.findTable (name! "users") = some caseTable := by decide +kernel
example : nullUsers.raw.catalog.findTable (name! "users") = some nullTable := by decide +kernel

/-- The groups that the query makes of the rows of `users`: grouped by `email` (the cell `index`) under the collation of
that column. -/
abbrev emailGroups (db : Database) (position index : Nat) (table : CatalogTable) : List (List (List Value)) :=
  Resolved.groups (Resolved.EvalContext.bound []) [(.column index, (table.columns[index]?.map (·.collation)).getD .binary)]
    (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] })

/-- The query of the fixture: no two users have the same email. -/
def uniqueEmails : Script := sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM users GROUP BY email HAVING count(*) > 1)"

/-- Over every database that has a table `users` with a column `email` at position `index`, the claims of
`noDuplicateKeys_claims` for `uniqueEmails`: it holds exactly when each group of the rows by the cell `index`, under
the collation of the column, has at most one row, it is empty exactly when not, and it does not fail. Proof sketch:
`noDuplicateKeys_claims` with the result column `1` (`resultColumn_one_facts`), no `WHERE` and the group key of the
column (`GroupTermResolves.identifier_table`). -/
theorem email_claims (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "users") = some (position, table))
    (column : columnPosition table.columns (name! "email") = some index) :
    (Holds uniqueEmails db ↔ keyGroupsShort db [] position table none (.column index)
        ((table.columns[index]?.map (·.collation)).getD .binary) = true) ∧
      (Empty uniqueEmails db ↔ keyGroupsShort db [] position table none (.column index)
        ((table.columns[index]?.map (·.collation)).getD .binary) = false) ∧
      ¬ Fails uniqueEmails db := by
  obtain ⟨notCall, noCalls, columns, grouped, feeds⟩ := resultColumn_one_facts runContext.profile.dqsDml
    (tableScope db.raw.catalog { table := name! "users", alias := none } position table)
    { current := some 0, aggregates := [.callStar "count"] } (.column index)
  exact noDuplicateKeys_claims (head := rfl) (count := rfl) (namedSource := rfl) (current := rfl) (arguments := rfl)
    found notCall noCalls columns grouped feeds (FilterResolves.of_none _ _ _ _)
    (GroupTermResolves.identifier_table column).toIn (by simp) (Resolved.Expr.calm_literal _)
    (Resolved.Expr.calm_column index)

/-- Over every database that has a table `users` with a column `email` at position `index`, "no two users have the
same email" is a claim about the groups of rows with equal emails, as `GROUP BY` makes them: the query holds exactly
when no group has more than one row. Proof sketch: `email_claims`; without `WHERE` every row is kept
(`Resolved.keptRows_none`). -/
theorem every_email_is_unique (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "users") = some (position, table))
    (column : columnPosition table.columns (name! "email") = some index) :
    Holds uniqueEmails db ↔ ∀ group ∈ emailGroups db position index table, group.length ≤ 1 := by
  simpa [emailGroups, Resolved.keptRows_none, List.all_eq_true] using (email_claims db position index table found column).1

/-- Over every database as in `every_email_is_unique`, the query is empty exactly when some group has more than one
row, which is some pair of users with an equal email (two NULL emails are equal for `GROUP BY`). -/
theorem some_email_is_repeated (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "users") = some (position, table))
    (column : columnPosition table.columns (name! "email") = some index) :
    Empty uniqueEmails db ↔ ∃ group ∈ emailGroups db position index table, 1 < group.length := by
  simpa [emailGroups, Resolved.keptRows_none, List.all_eq_false, Nat.not_le] using
    (email_claims db position index table found column).2.1

/-- Over every database as in `every_email_is_unique`, the query does not fail. -/
theorem email_check_does_not_fail (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "users") = some (position, table))
    (column : columnPosition table.columns (name! "email") = some index) :
    ¬ Fails uniqueEmails db :=
  (email_claims db position index table found column).2.2

/-- The guide's claim, over every database that has a table `users` with a column `email` at position `index`: the query
holds exactly when no user has an email that compares as equal, under the collation of the column, to the email of a
user before it in scan order. Two users with NULL emails compare as equal here, unlike under a `UNIQUE` index. Proof
sketch: `email_claims` and `keyGroupsShort_iff_pairwise`, and the key `.column index` reads the cell `index`. -/
theorem no_two_users_share_an_email (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "users") = some (position, table))
    (column : columnPosition table.columns (name! "email") = some index) :
    Holds uniqueEmails db ↔
      (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).Pairwise
        fun (earlier later : List Value) => ((table.columns[index]?.map CatalogColumn.collation).getD .binary).compare
          (later.getD index .null) (earlier.getD index .null) ≠ Ordering.eq := by
  rw [(email_claims db position index table found column).1, keyGroupsShort_iff_pairwise]
  simp [Resolved.keptRows_none, Resolved.Expr.eval_column]

/-- Over every database as in `no_two_users_share_an_email`, the query is empty exactly when some user has an email that
compares as equal to the email of a user before it. Proof sketch: as for `no_two_users_share_an_email`, with the
`Empty` claim of `email_claims`. -/
theorem two_users_share_an_email (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "users") = some (position, table))
    (column : columnPosition table.columns (name! "email") = some index) :
    Empty uniqueEmails db ↔
      ¬ (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }).Pairwise
        fun (earlier later : List Value) => ((table.columns[index]?.map CatalogColumn.collation).getD .binary).compare
          (later.getD index .null) (earlier.getD index .null) ≠ Ordering.eq := by
  rw [(email_claims db position index table found column).2.1, ← Bool.not_eq_true, keyGroupsShort_iff_pairwise]
  simp [Resolved.keptRows_none, Resolved.Expr.eval_column]

-- The instance with addresses that differ only in case, in the pairwise form: both sides agree.
example : Empty uniqueEmails caseUsers :=
  (two_users_share_an_email caseUsers caseTable.1 1 caseTable.2 (by decide +kernel)
    (by decide +kernel)).2 (by decide +kernel)

-- The instance with three different addresses, in the pairwise form: both sides agree.
example : Holds uniqueEmails distinctUsers :=
  (no_two_users_share_an_email distinctUsers distinctTable.1 1 distinctTable.2 (by decide +kernel)
    (by decide +kernel)).2 (by decide +kernel)

-- The instance with three different addresses: the query holds, and no group has two rows.
example : Holds uniqueEmails distinctUsers :=
  (every_email_is_unique distinctUsers distinctTable.1 1 distinctTable.2 (by decide +kernel)
    (by decide +kernel)).2 (by decide +kernel)

-- The instance with addresses that differ only in case: `NOCASE` puts them in one group, so the query is empty.
example : Empty uniqueEmails caseUsers :=
  (some_email_is_repeated caseUsers caseTable.1 1 caseTable.2 (by decide +kernel)
    (by decide +kernel)).2 (by decide +kernel)

-- The instance with two NULL addresses: they are one group, so the query is empty.
example : Empty uniqueEmails nullUsers :=
  (some_email_is_repeated nullUsers nullTable.1 1 nullTable.2 (by decide +kernel)
    (by decide +kernel)).2 (by decide +kernel)

-- Both sides agree on the instance with a repeated address: the query does not hold.
example : ¬ Holds uniqueEmails caseUsers :=
  fun holds => absurd ((every_email_is_unique caseUsers caseTable.1 1 caseTable.2 (by decide +kernel)
    (by decide +kernel)).1 holds) (by decide +kernel)

-- The group-based Empty equivalence also has a false instance, with distinct keys on both sides.
example : ¬ Empty uniqueEmails distinctUsers := by
  rw [some_email_is_repeated distinctUsers distinctTable.1 1 distinctTable.2 (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The pairwise Empty equivalence has the same false instance without relying on the group equivalence.
example : ¬ Empty uniqueEmails distinctUsers := by
  rw [two_users_share_an_email distinctUsers distinctTable.1 1 distinctTable.2 (by decide +kernel) (by decide +kernel)]
  decide +kernel
example : ¬ Holds uniqueEmails caseUsers := by
  rw [no_two_users_share_an_email caseUsers caseTable.1 1 caseTable.2 (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- Duplicate keys change row existence, while both catalog-valid queries remain free of errors.
example : ¬ Fails uniqueEmails distinctUsers :=
  email_check_does_not_fail distinctUsers distinctTable.1 1 distinctTable.2 (by decide +kernel) (by decide +kernel)
example : ¬ Fails uniqueEmails caseUsers :=
  email_check_does_not_fail caseUsers caseTable.1 1 caseTable.2 (by decide +kernel) (by decide +kernel)

#print axioms every_email_is_unique
#print axioms some_email_is_repeated
#print axioms email_check_does_not_fail
#print axioms no_two_users_share_an_email
#print axioms two_users_share_an_email
