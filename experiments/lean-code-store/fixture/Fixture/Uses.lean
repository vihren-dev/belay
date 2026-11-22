import Fixture.Derive

/-! Fixture: uses of declarations of other modules, and uses outside each declaration. -/

/-- Asks for the equation lemmas of `describe` in this module. -/
theorem describe_red : describe .red = "r" := by simp [describe]

/-- Uses the derived `Hashable` instance of `Point`. -/
def hashPoint (p : Point) : UInt64 := hash p

attribute [simp] usesSecret

#check Foo
