import Belay.Sqlite.Model

set_option doc.verso true

/-! Statement syntax with the source range of each node (ADR 0017, S1, prototype 2, candidate
A). The port of {lit}`belay/sqlite/located.py`: a model restriction names a statement index and
a node path, and each path step is the position of a constructor argument or a structure field,
then the index in a list. A located value holds the model's syntax value and a tree of ranges in
that shape, so that a path selects the range of the node that a restriction refers to. -/

namespace Belay.Sqlite.Translation

/-- The half-open UTF-8 byte range of a syntax node in the SQL text and the ranges of its parts
in path order: the constructor arguments or fields, or the list items. For example, the name
{lit}`t` at bytes 14 to 15 has {lit}`{ start := 14, stop := 15 }`. -/
structure Span where
  /-- The first byte of the range. -/
  start : Nat
  /-- The byte after the range. -/
  stop : Nat
  /-- The ranges of the parts, in path order. -/
  parts : Array Span := #[]
  deriving Inhabited, BEq, Repr

/-- A syntax value of the model and its ranges ({name}`Span`). -/
structure Located (α : Type) where
  /-- The value, for example a {lit}`Syntax.Statement`. -/
  value : α
  /-- The ranges of the value and of its parts. -/
  span : Span
  deriving Inhabited

/-- A value without located parts, such as a name or a flag. -/
def leaf (value : α) (start stop : Nat) : Located α := { value, span := { start, stop } }

/-- A value with the ranges of its parts, in path order. -/
def composite (value : α) (start stop : Nat) (parts : Array Span) : Located α :=
  { value, span := { start, stop, parts } }

/-- A list value whose path steps are the item indexes. -/
def sequence (items : Array (Located α)) (start stop : Nat) : Located (List α) :=
  composite (items.toList.map (·.value)) start stop (items.map (·.span))

/-- The value changed by the function, with the same ranges. -/
def Located.map (change : α → β) (item : Located α) : Located β := { item with value := change item.value }

/-- A present optional part: the value in {lit}`some`, with its own ranges, as the model's path
steps do not count the {lit}`some`. -/
def Located.present (item : Located α) : Located (Option α) := item.map some

/-- An absent optional part at the range of its clause. -/
def missing (start stop : Nat) : Located (Option α) := leaf none start stop

/-- A Lean pair. -/
def pair (first : Located α) (second : Located β) (start stop : Nat) : Located (α × β) :=
  composite (first.value, second.value) start stop #[first.span, second.span]

end Belay.Sqlite.Translation
