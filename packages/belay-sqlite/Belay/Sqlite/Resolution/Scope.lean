import Belay.Sqlite.Resolution.Catalog

set_option doc.verso true

/-! The names in scope of an expression (ADR 0012, amendment 2, "Names"): the sources of
a query or the one table of a write, each with its name and columns. A joined row is
the concatenation of the cells of the sources in order, so a column has a position in
that row. -/

namespace Belay.Sqlite

/-- How the join of a source that merges a column changes an unqualified name of that
column (ADR 0012, amendment 3): an inner or left join keeps the left result, a right join
takes its own column, and a full join adds its column to a coalesce. -/
inductive MergeRule where
  /-- An inner or left join: the name keeps naming the left result. -/
  | keepLeft
  /-- A right join: the name names this source's column, with its affinity. -/
  | takeRight
  /-- A full join: the name is the coalesce of the left result and this column. -/
  | coalesce
  deriving Repr, DecidableEq

/-- One named source: the name that qualifies its columns (the alias as written, else the
table name as declared, or {lit}`json_each` for that function), its columns, the position
of its first cell in the joined row, and the columns that a {lit}`USING` or {lit}`NATURAL`
join merged into a left column. -/
structure ScopeSource where
  /-- The name of the source. -/
  name : Identifier
  /-- The columns of the source's table. -/
  columns : List CatalogColumn
  /-- The position in the joined row of the source's first cell: the number of cells of
  the sources before it ({lit}`Scope.place`). 0 for the first source and for the table of a
  write. -/
  offset : Nat := 0
  /-- The positions in {name}`ScopeSource.columns` of the merged columns: {lit}`*` and
  unqualified names do not see them, and qualified names and {lit}`x.*` do. Empty for a
  source without {lit}`USING` or {lit}`NATURAL`, and for the table of a write. -/
  merged : List Nat := []
  /-- How the source's join changes an unqualified name of a merged column; the rule of
  an inner join for a source that merges nothing. -/
  mergeRule : MergeRule := .keepLeft
  /-- The positions in {name}`ScopeSource.columns` of the hidden columns, which {lit}`*` and
  {lit}`x.*` do not show and names do see: the {lit}`json` and {lit}`root` columns of
  {lit}`json_each`. Empty for a table. -/
  hidden : List Nat := []
  deriving Repr, DecidableEq

/-- The sources in scope, in {lit}`FROM` order, each at its offset in the joined row;
empty where no table is in scope, as in a {lit}`VALUES` row. -/
abbrev Scope := List ScopeSource

/-- The sources in order, each at the offset after the cells of the sources before it. -/
def Scope.place (sources : List ScopeSource) : Scope :=
  (sources.foldl (fun (offset, placed) source =>
    (offset + source.columns.length, placed ++ [{ source with offset }])) (0, [])).2

/-- The scope of one table under its name, as a write or a query of one table has. -/
def Scope.single (name : Identifier) (columns : List CatalogColumn) : Scope := [{ name, columns }]

/-- The columns of all sources, in the order of the concatenated row. -/
def Scope.columns (scope : Scope) : List CatalogColumn := scope.flatMap (·.columns)

/-- The number of cells before the source at {lit}`index`: its offset, or the number of
cells of the whole scope for an index past its end. -/
def Scope.cellsBefore (scope : Scope) (index : Nat) : Nat :=
  (scope[index]?.map (·.offset)).getD scope.columns.length

/-- The columns of a source with their positions in the joined row that pass the filter
on their positions in the source. -/
def ScopeSource.placedColumns (source : ScopeSource) (keep : Nat → Bool) : List (Nat × CatalogColumn) :=
  ((source.columns.mapIdx fun index column => (index, column)).filter (keep ·.1)).map
    fun (index, column) => (source.offset + index, column)

/-- The columns that {lit}`*` reads, with their positions in the concatenated row: every
column of every source that is not merged ({name}`ScopeSource.merged`) or hidden
({name}`ScopeSource.hidden`). -/
def Scope.visible (scope : Scope) : List (Nat × CatalogColumn) :=
  scope.flatMap fun source => source.placedColumns fun index => !source.merged.contains index && !source.hidden.contains index

/-- The positions in the concatenated row of the columns that an unqualified name
names: the first column with the folded name in each source that has one, unless that
column is merged ({name}`ScopeSource.merged`). One position is a name; none is a missing
name; two or more are SQLite's {lit}`ambiguous column name`. -/
def Scope.matches (scope : Scope) (name : Identifier) : List Nat :=
  scope.flatMap fun source =>
    (((columnPosition source.columns name).filter (!source.merged.contains ·)).map (source.offset + ·)).toList

/-- The resolution of an unqualified name over a scope: no column, two columns that no
join merges, or the position of the first column of the name with the positions whose
coalesce the name reads; one position is that column itself. -/
inductive NameResolution where
  /-- No source has a column of the name. -/
  | missing
  /-- Two sources have a column of the name that no join merged: SQLite's
  {lit}`ambiguous column name`. -/
  | ambiguous
  /-- The name: {lit}`first` is the position of its first column, and {lit}`reads` the
  positions of the columns that it reads, as their coalesce when there are several. -/
  | found (first : Nat) (reads : List Nat)
  deriving Repr, DecidableEq

/-- One step of {lit}`Scope.resolveName`: the next source after the result so far. A
column of the name in the first source with one gives it; a later one changes the result
only when the source's join merged it, by its {name}`MergeRule`, and makes the name
ambiguous otherwise. -/
def Scope.resolveStep (name : Identifier) (result : NameResolution) (source : ScopeSource) : NameResolution :=
  match columnPosition source.columns name, result with
  | none, result => result
  | some index, .missing => .found (source.offset + index) [source.offset + index]
  | some _, .ambiguous => .ambiguous
  | some index, .found first reads =>
    if source.merged.contains index then match source.mergeRule with
      | .keepLeft => .found first reads
      | .takeRight => .found first [source.offset + index]
      | .coalesce => .found first (reads ++ [source.offset + index])
    else .ambiguous

/-- Resolve an unqualified name over the sources from left to right, as SQLite does
(checked on native 3.51.0), by {name}`Scope.resolveStep`: the first source with a column
of the folded name gives that column; a later one changes the result only when its join
merged the name; a later one that did not merge it makes the name ambiguous. -/
def Scope.resolveName (scope : Scope) (name : Identifier) : NameResolution :=
  scope.foldl (Scope.resolveStep name) .missing

/-- Whether the source has the folded name. -/
def ScopeSource.named (source : ScopeSource) (name : Identifier) : Bool :=
  source.name.sameName name

/-- Whether a source of the scope has the folded name. -/
def Scope.hasSource (scope : Scope) (name : Identifier) : Bool :=
  scope.any (·.named name)

/-- Resolve the qualified name {lit}`source.column` as SQLite does (checked on native 3.51.0):
as an unqualified name ({name}`Scope.resolveName`) over only the sources with the folded
name {lit}`source`, so a column of two such sources that no join merged is SQLite's
{lit}`ambiguous column name`, and merged columns are visible. -/
def Scope.resolveQualified (scope : Scope) (source column : Identifier) : NameResolution :=
  Scope.resolveName (scope.filter (·.named source)) column

/-- The columns of {lit}`source.*` with their positions in the concatenated row: every
column that is not hidden ({name}`ScopeSource.hidden`) of every source with the folded
name, in order, merged columns included; none when no source has the name. -/
def Scope.starColumns? (scope : Scope) (name : Identifier) : Option (List (Nat × CatalogColumn)) :=
  if scope.hasSource name then
    some ((scope.filter (·.named name)).flatMap fun source => source.placedColumns (!source.hidden.contains ·))
  else none

/-- Whether a name resolution reads only its first column: missing, ambiguous, or found
with the one position of its first column. -/
def NameResolution.single : NameResolution → Prop
  | .found first reads => reads = [first]
  | .missing | .ambiguous => True

/-- For every scope whose sources all keep the left result ({name}`MergeRule.keepLeft`), as
in a {lit}`FROM` without right and full joins, and every name, the resolution of the name
reads only its first column ({name}`NameResolution.single`): a name is one column, as in
slice 4b. Proof sketch: each step of {name}`Scope.resolveStep` keeps the property, since a
merged column under {name}`MergeRule.keepLeft` keeps the result and any other later
column makes the name ambiguous. -/
theorem resolveName_single (scope : Scope) (keep : ∀ source ∈ scope, source.mergeRule = .keepLeft)
    (name : Identifier) : (scope.resolveName name).single := by
  have step : ∀ (sources : Scope) (state : NameResolution), state.single →
      (∀ source ∈ sources, source.mergeRule = .keepLeft) →
      (sources.foldl (Scope.resolveStep name) state).single := by
    intro sources
    induction sources with
    | nil => intro state holds _; exact holds
    | cons source rest ih =>
      intro state holds keeps
      apply ih _ _ fun other member => keeps other (List.mem_cons_of_mem _ member)
      have rule := keeps source List.mem_cons_self
      unfold Scope.resolveStep
      split
      · exact holds
      · simp [NameResolution.single]
      · simp [NameResolution.single]
      · split
        · simp only [rule]; exact holds
        · first | (simp [NameResolution.single]; done) | simpa [NameResolution.single] using holds
  exact step scope .missing trivial keep

end Belay.Sqlite
