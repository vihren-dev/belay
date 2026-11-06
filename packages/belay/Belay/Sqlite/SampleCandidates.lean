import Belay.Sqlite.SampleConstraints

set_option doc.verso true

/-! The generated candidate databases of SQL counterexample search, in the order of the search:
the targeted databases, the small table contents, fewest rows first, and seeded
random databases. The checker computes them with compiled code and screens each one; every
candidate that it reports is certified separately. -/

namespace Belay.Sqlite.Sampling

/-- The sequences of the given length of positions in a list of the given size that never
decrease, in lexicographic order. They choose a multiset of values of the pool for the rows of
one table, so that two orders of the same rows count once. For example, length two and size
two give {lit}`[0, 0]`, {lit}`[0, 1]` and {lit}`[1, 1]`. -/
def nondecreasing : (length size : Nat) → (start : Nat := 0) → List (List Nat)
  | 0, _, _ => [[]]
  | length + 1, size, start =>
    (List.range' start (size - start)).flatMap fun first =>
      (nondecreasing length size first).map (first :: ·)

/-- Visit each content of the tables of the catalog with exactly the given number of rows in
total and at most {lit}`maxRows` rows in each table. Each row has one value of the pool in every
column ({name}`uniform` does the same). The cells are given for each object of the catalog; views,
indexes, triggers and the tables that {lit}`fill` rejects get none. The visit returns true to
stop; the result says whether a visit stopped. -/
def visitContents [Monad m] (pool : List Value) (maxRows : Nat) (fill : Model.CatalogObject → Bool)
    (visit : List (List (List Value)) → m Bool) :
    (objects : List Model.CatalogObject) → (remaining : Nat) → (cells : List (List (List Value))) → m Bool
  | [], remaining, cells => if remaining == 0 then visit cells.reverse else pure false
  | object :: objects, remaining, cells => do
    match object.entry with
    | .table table =>
      if !fill object then return ← visitContents pool maxRows fill visit objects remaining ([] :: cells)
      for count in List.range (min maxRows remaining + 1) do
        for positions in nondecreasing count pool.length do
          let rows := positions.map fun position =>
            List.replicate table.columns.length (pool.getD position .null)
          if ← visitContents pool maxRows fill visit objects (remaining - count) (rows :: cells) then return true
      return false
    | .index _ | .trigger _ | .view _ => visitContents pool maxRows fill visit objects remaining ([] :: cells)

/-- A seeded random database for the search: Plausible's cells ({name}`selectCells`) for the
tables that the search fills ({name}`fills`), with the simple constraints
({name}`constrainedCells`). It fails when {name}`validated` rejects the result. -/
def touchedDatabase (base : Database) (constants : List Value) (maxRows : Nat)
    (touched : Option (List Model.Identifier)) (fallback : Value) : Plausible.Gen Database := do
  let cells ← selectCells base.raw.catalog
    ((·.val) <$> Plausible.Gen.choose Nat 0 maxRows (Nat.zero_le _)) (value constants)
  let cells := (base.raw.catalog.zip cells).map fun (object, rows) => if fills touched object then rows else []
  match validated (withCells base.raw (constrainedCells base.raw.catalog fallback cells)) with
  | some candidate => return candidate
  | none => throw (.genError "generated rows violate the supplied database constraints")

/-- The targeted databases ({name}`targeted`) of the search on a schema, with at most
{lit}`maxRows` rows in each table, and only the rows of the touched tables ({name}`onlyTouched`).
Their rows are not changed for the constraints: they test the edges of the constraints on
purpose, for example duplicate rows and NULL cells. -/
def touchedTargeted (base : Database) (constants : List Value) (touched : Option (List Model.Identifier))
    (maxRows : Nat) : List Database :=
  let base := (validated (onlyTouched touched base.raw)).getD base
  (targeted base constants).filterMap fun database => do
    let database ← validated (onlyTouched touched database.raw)
    if database.raw.rows.all (·.length ≤ maxRows) then some database else none

/-- The first candidates of the search on a schema, at most {lit}`limit` of them, in this order:
the targeted databases ({name}`touchedTargeted`); each valid content of the tables with at most {lit}`maxRows` rows in each table,
fewest rows in total first ({name}`visitContents`): each row selects one pool value for every
column, and each multiset of selected values per table comes once; and {lit}`randomCount`
seeded databases ({name}`touchedDatabase`) with the seeds from {lit}`seed`. Only the touched
tables ({name}`fills`; none for every table) have rows: the other tables are empty in every
candidate. The contents and the seeded databases satisfy the simple constraints
({name}`constrainedCells`), with the first pool value that is not NULL for a NOT NULL column.
The stored rows can differ from the selection, and two selections can give the same database,
because the constraints, column affinity and rowid assignment ({name}`withCells`) apply after
it. The pool is the claim's constants, then {name}`boundaryValues`. The list ends after the
first candidate for which {lit}`stop` holds, given its position and the candidate, so that a
caller can screen the candidates while they are generated. The list is finite and explicit; a
caller can screen it, or supply other candidates to the checker. -/
def candidates (base : Database) (constants : List Value) (touched : Option (List Model.Identifier))
    (maxRows randomCount seed size limit : Nat) (stop : Nat → Database → Bool := fun _ _ => false) :
    Array Database := Id.run do
  let pool := (constants ++ boundaryValues).eraseDups
  let fallback := (pool.find? fun value => !value matches .null).getD (.integer 0)
  let catalog := base.raw.catalog
  -- Add a candidate; true when the list is complete: the limit or the stop.
  let add (found : Array Database) (database : Database) : Array Database × Bool :=
    (found.push database, found.size + 1 ≥ limit || stop found.size database)
  let mut found : Array Database := #[]
  if limit == 0 then return found
  for database in touchedTargeted base constants touched maxRows do
    let (next, done) := add found database
    found := next
    if done then return found
  let base := (validated (onlyTouched touched base.raw)).getD base
  let tables := catalog.countP (fills touched)
  let ((), (contents, done)) := (do
    for total in List.range (tables * maxRows + 1) do
      let full ← visitContents pool maxRows (fills touched) (fun cells => do
          if let some database := validated (withCells base.raw (constrainedCells catalog fallback cells)) then
            let (found, _) ← get
            set (add found database)
          return (← get).2)
        catalog total []
      if full then return ()
    : StateM (Array Database × Bool) Unit).run (found, false)
  found := contents
  if done then return found
  for index in List.range randomCount do
    if let .ok database := seeded (touchedDatabase base constants maxRows touched fallback) (seed + index) size then
      let (next, done) := add found database
      found := next
      if done then return found
  return found

end Belay.Sqlite.Sampling
