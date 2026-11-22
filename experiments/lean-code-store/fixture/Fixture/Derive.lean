import Fixture.Types

/-! Fixture: `deriving instance` commands with comments, and an ordinary instance after a block
comment that contains the words of such a command at the start of a line. -/

deriving instance BEq, Hashable for Point, Tag

deriving instance Repr for -- a comment inside the type list
  Tag

/- This comment is not a command:
deriving instance Inhabited for Tag -/
instance : Inhabited Tag := ⟨Tag.first⟩

deriving instance -- deriving instance
  Ord for Tag
