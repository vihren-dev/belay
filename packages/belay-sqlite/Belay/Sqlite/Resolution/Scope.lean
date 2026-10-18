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
table name as declared, or {lit}`json_each` for that function), its columns, and the columns that a {lit}`USING` or {lit}`NATURAL`
join merged into a left column. -/
structure ScopeSource where
  /-- The name of the source. -/
  name : String
  /-- The columns of the source's table. -/
  columns : List CatalogColumn
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

/-- The sources in scope, in {lit}`FROM` order; empty where no table is in scope, as in
a {lit}`VALUES` row. -/
abbrev Scope := List ScopeSource

/-- The scope of one table under its name, as a write or a query of one table has. -/
def Scope.single (name : String) (columns : List CatalogColumn) : Scope := [{ name, columns }]

/-- The columns of all sources, in the order of the concatenated row. -/
def Scope.columns (scope : Scope) : List CatalogColumn := scope.flatMap (·.columns)

/-- The columns that {lit}`*` reads, with their positions in the concatenated row: every
column of every source that is not merged ({name}`ScopeSource.merged`) or hidden
({name}`ScopeSource.hidden`). -/
def Scope.visible (scope : Scope) : List (Nat × CatalogColumn) :=
  (scope.foldl (fun (offset, found) source =>
    (offset + source.columns.length, found ++ ((source.columns.mapIdx fun index column => (index, column)).filter
      fun (index, _) => !source.merged.contains index && !source.hidden.contains index).map
        fun (index, column) => (offset + index, column)))
    (0, [])).2

/-- The positions in the concatenated row of the columns that an unqualified name
names: the first column with the folded name in each source that has one, unless that
column is merged ({name}`ScopeSource.merged`). One position is a name; none is a missing
name; two or more are SQLite's {lit}`ambiguous column name`. -/
def Scope.matches (scope : Scope) (name : String) : List Nat :=
  (scope.foldl (fun (offset, found) source =>
    (offset + source.columns.length, found ++ (((columnPosition source.columns name).filter
      (!source.merged.contains ·)).map (offset + ·)).toList))
    (0, [])).2

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

/-- One step of {lit}`Scope.resolveName`: the next source, at the offset of its first
cell, after the result so far. A column of the name in the first source with one gives
it; a later one changes the result only when the source's join merged it, by its
{name}`MergeRule`, and makes the name ambiguous otherwise. -/
def Scope.resolveStep (name : String) (state : Nat × NameResolution) (source : ScopeSource) : Nat × NameResolution :=
  let (offset, result) := state
  (offset + source.columns.length, match columnPosition source.columns name, result with
    | none, result => result
    | some index, .missing => .found (offset + index) [offset + index]
    | some _, .ambiguous => .ambiguous
    | some index, .found first reads =>
      if source.merged.contains index then match source.mergeRule with
        | .keepLeft => .found first reads
        | .takeRight => .found first [offset + index]
        | .coalesce => .found first (reads ++ [offset + index])
      else .ambiguous)

/-- Resolve an unqualified name over the sources from left to right, as SQLite does
(checked on native 3.51.0), by {name}`Scope.resolveStep`: the first source with a column
of the folded name gives that column; a later one changes the result only when its join
merged the name; a later one that did not merge it makes the name ambiguous. -/
def Scope.resolveName (scope : Scope) (name : String) : NameResolution :=
  (scope.foldl (Scope.resolveStep name) (0, .missing)).2

/-- Whether a source of the scope has the folded name. -/
def Scope.hasSource (scope : Scope) (name : String) : Bool :=
  scope.any fun source => normalizeIdentifier source.name == normalizeIdentifier name

/-- One step of {lit}`Scope.resolveQualified`: {name}`Scope.resolveStep` for a source with the
folded name {lit}`sourceName`, and only the offset of the next source for any other. -/
def Scope.qualifiedStep (sourceName column : String) (state : Nat × NameResolution) (source : ScopeSource) :
    Nat × NameResolution :=
  if normalizeIdentifier source.name == normalizeIdentifier sourceName then Scope.resolveStep column state source
  else (state.1 + source.columns.length, state.2)

/-- Resolve the qualified name {lit}`source.column` as SQLite does (checked on native 3.51.0):
as an unqualified name ({name}`Scope.resolveName`) over only the sources with the folded
name {lit}`source`, so a column of two such sources that no join merged is SQLite's
{lit}`ambiguous column name`, and merged columns are visible. -/
def Scope.resolveQualified (scope : Scope) (source column : String) : NameResolution :=
  (scope.foldl (Scope.qualifiedStep source column) (0, .missing)).2

/-- The columns of {lit}`source.*` with their positions in the concatenated row: every
column that is not hidden ({name}`ScopeSource.hidden`) of every source with the folded
name, in order, merged columns included; none when no source has the name. -/
def Scope.starColumns? (scope : Scope) (name : String) : Option (List (Nat × CatalogColumn)) :=
  if scope.hasSource name then
    some (scope.foldl (fun (offset, found) source =>
      (offset + source.columns.length,
        if normalizeIdentifier source.name == normalizeIdentifier name then
          found ++ ((source.columns.mapIdx fun index column => (index, column)).filter (!source.hidden.contains ·.1)).map
            fun (index, column) => (offset + index, column)
        else found)) (0, [])).2
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
    (name : String) : (scope.resolveName name).single := by
  have step : ∀ (sources : Scope) (state : Nat × NameResolution), state.2.single →
      (∀ source ∈ sources, source.mergeRule = .keepLeft) →
      (sources.foldl (Scope.resolveStep name) state).2.single := by
    intro sources
    induction sources with
    | nil => intro state holds _; exact holds
    | cons source rest ih =>
      intro state holds keeps
      apply ih _ _ fun other member => keeps other (List.mem_cons_of_mem _ member)
      obtain ⟨offset, result⟩ := state
      have rule := keeps source List.mem_cons_self
      unfold Scope.resolveStep
      dsimp only
      split
      · exact holds
      · simp [NameResolution.single]
      · simp [NameResolution.single]
      · split
        · simp only [rule]; exact holds
        · first | (simp [NameResolution.single]; done) | simpa [NameResolution.single] using holds
  exact step scope (0, .missing) trivial keep

end Belay.Sqlite
