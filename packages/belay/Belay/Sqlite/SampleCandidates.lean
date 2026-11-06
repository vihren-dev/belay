import Belay.Sqlite.SampleDatabases

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
indexes and triggers get none. The visit returns true to stop; the result says whether a visit
stopped. -/
def visitContents [Monad m] (pool : List Value) (maxRows : Nat) (visit : List (List (List Value)) → m Bool) :
    (objects : List Model.CatalogObject) → (remaining : Nat) → (cells : List (List (List Value))) → m Bool
  | [], remaining, cells => if remaining == 0 then visit cells.reverse else pure false
  | object :: objects, remaining, cells => do
    match object.entry with
    | .table table =>
      for count in List.range (min maxRows remaining + 1) do
        for positions in nondecreasing count pool.length do
          let rows := positions.map fun position =>
            List.replicate table.columns.length (pool.getD position .null)
          if ← visitContents pool maxRows visit objects (remaining - count) (rows :: cells) then return true
      return false
    | .index _ | .trigger _ | .view _ => visitContents pool maxRows visit objects remaining ([] :: cells)

/-- The first candidates of the search on a schema, at most {lit}`limit` of them, in this order:
the targeted databases ({name}`targeted`) with at most {lit}`maxRows` rows in
each table; each valid content of the tables with at most {lit}`maxRows` rows in each table,
fewest rows in total first ({name}`visitContents`): each row selects one pool value for every
column, and each multiset of selected values per table comes once. The stored rows can differ
from the selection, and two selections can give the same database, because column affinity
and rowid assignment ({name}`withCells`) apply after it;
and {lit}`randomCount` databases of {name}`database` with the seeds from {lit}`seed`. The pool is
the claim's constants, then {name}`boundaryValues`. The list is finite and explicit; a caller can
screen it, or supply other candidates to the checker. -/
def candidates (base : Database) (constants : List Value) (maxRows randomCount seed size limit : Nat) :
    Array Database := Id.run do
  let pool := (constants ++ boundaryValues).eraseDups
  let mut found : Array Database := #[]
  for database in targeted base constants do
    if found.size ≥ limit then return found
    if database.raw.rows.all (·.length ≤ maxRows) then found := found.push database
  if found.size ≥ limit then return found
  let tables := base.raw.catalog.countP fun object => object.entry matches .table _
  let (_, contents) := (do
    for total in List.range (tables * maxRows + 1) do
      let full ← visitContents pool maxRows (fun cells => do
          if let some database := validated (withCells base.raw cells) then modify (·.push database)
          return (← get).size ≥ limit)
        base.raw.catalog total []
      if full then return ()
    : StateM (Array Database) Unit).run found
  found := contents
  for index in List.range randomCount do
    if found.size ≥ limit then return found
    if let .ok database := seeded (database base constants maxRows) (seed + index) size then
      found := found.push database
  return found

end Belay.Sqlite.Sampling
