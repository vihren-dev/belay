import Fixture.Derive

/-! Fixture: uses of declarations of other modules, uses outside each declaration, and an
`initialize` command, whose macro-scoped constant rule 4 makes a declaration. -/

/-- Asks for the equation lemmas of `describe` in this module. -/
theorem describe_red : describe .red = "r" := by simp [describe]

/-- Uses the derived `Hashable` instance of `Point`. -/
def hashPoint (p : Point) : UInt64 := hash p

attribute [simp] usesSecret

#check Foo

/-- An `initialize` command: Lean adds a constant with a macro-scoped name and the same range. -/
initialize counter : IO.Ref Nat ← IO.mkRef 0

/-- A written definition that the next command makes an instance. -/
def inhabitedPoint : Inhabited Point := ⟨⟨0, 0⟩⟩

attribute [instance] inhabitedPoint
