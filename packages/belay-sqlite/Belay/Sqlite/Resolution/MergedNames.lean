import Belay.Sqlite.Resolution.Scope
import Belay.Sqlite.Resolution.QueryAffinity

set_option doc.verso true

/-! The operands of unqualified names over a scope with merged columns (ADR 0012,
amendment 3; slice 4d): a name that reads one column is that column with its affinity,
and a name that reads several, after full joins, is their coalesce, which has no
affinity, as in SQLite. -/

namespace Belay.Sqlite

/-- The coalesce of the columns at the positions, in order: the first column that is not
NULL. One position is that column; no position, which {name}`Scope.resolveName` never
gives, is NULL. -/
def coalesceColumns : List Nat → Resolved.Expr
  | [] => .literal .null
  | [position] => .column position
  | position :: rest => .coalesce (.column position) (coalesceColumns rest)

/-- The operand of a name that reads the columns at the positions
({name}`NameResolution.found`): one column with its affinity, or the coalesce of several
with no affinity. -/
def Scope.nameOperand (scope : Scope) : List Nat → Operand
  | [position] => (.column position, scope.columns[position]?.map CatalogColumn.affinity)
  | reads => (coalesceColumns reads, none)

/-- The index of the source whose cells hold the position of the concatenated row; the
number of sources for a position after the last cell. -/
def Scope.sourceOf (scope : Scope) (position : Nat) : Nat :=
  (scope.foldl (fun (offset, index, found) source =>
    if found.isNone && position < offset + source.columns.length then (offset + source.columns.length, index + 1, some index)
    else (offset + source.columns.length, index + 1, found)) (0, 0, none)).2.2.getD scope.length

/-- The operand of the column at the position in the expansion of {lit}`*` or
{lit}`x.*`, as SQLite expands it (checked on native 3.51.0): when the column's source is
to the left of a right or full join and a later join merges the column's name, the
expansion is the unqualified name ({name}`Scope.resolveName`), so the column shows the
right column or the coalesce of a merged pair; otherwise the column itself. -/
def Scope.starOperand (scope : Scope) (position : Nat) (column : CatalogColumn) : Operand :=
  let later := scope.drop (scope.sourceOf position + 1)
  let rightAfter := later.any fun source => source.mergeRule != .keepLeft
  let mergedLater := later.any fun source => (columnPosition source.columns column.name).any (source.merged.contains ·)
  if rightAfter && mergedLater then match scope.resolveName column.name with
    | .found _ reads => scope.nameOperand reads
    | .missing | .ambiguous => scope.nameOperand [position]
  else scope.nameOperand [position]

end Belay.Sqlite
