set_option doc.verso true

/-! Fixture: written declarations of each kind that the folding rules must decide. -/

/-- A point in the plane. -/
structure Point where
  x : Nat
  y : Nat

/-- A point with a third coordinate. -/
structure Point3 extends Point where
  z : Nat

/-- A color with an inline {lit}`deriving` clause. -/
inductive Color where
  | red
  | green
  deriving Repr, DecidableEq

/-- A tag without a `deriving` clause; {lit}`Fixture.Derive` derives its instances. -/
inductive Tag where
  | first
  | second

/-- Something with an area. -/
class Area (α : Type) where
  area : α → Nat

instance : Area Point where
  area p := p.x * p.y

/-- The sum of the coordinates, with a {lit}`where` function. -/
def total (p : Point) : Nat := go p.x
where
  go (n : Nat) : Nat := n + p.y

private def secret : Nat := 3

/-- Uses {name}`total` in its docstring and {lit}`secret` in its body. -/
def usesSecret : Nat := secret + total ⟨1, 2⟩

/-- A function by pattern matching, which has a match function. -/
def describe : Color → String
  | .red => "r"
  | .green => "g"

/-- Uses only the generated constructor and projection of {lit}`Prod` of the library, which fold
into {lit}`Prod`. -/
def firstOfPair : Nat := (Prod.mk 1 2).1

example : total ⟨1, 2⟩ = 3 := rfl

/-- A written declaration with a name that looks generated. -/
def Foo._helper : Nat := 1

/-- The user of {name}`Foo._helper`. -/
def Foo : Nat := Foo._helper + 1
