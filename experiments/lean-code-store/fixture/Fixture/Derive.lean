import Fixture.Types

/-! Fixture: a `deriving instance` command for two classes and two types. -/

deriving instance BEq, Hashable for Point, Tag
