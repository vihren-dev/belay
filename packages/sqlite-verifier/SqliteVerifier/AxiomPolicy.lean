set_option doc.verso true

/-!
The axioms that a verified proof may depend on. The kernel gates and the proof
author's audit command read the one list below, so the local audit and the gate
cannot disagree (ADR 0010).
-/

namespace SqliteVerifier

/-- The foundational axioms that a proof may depend on: {name}`propext`,
{name}`Classical.choice` and {name}`Quot.sound`. A proof that depends on any other
axiom, including {name}`sorryAx`, is rejected. This list is fixed by the verifier,
not a setting:

```lean
#guard SqliteVerifier.allowedAxioms.contains `propext
```
-/
def allowedAxioms : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]

end SqliteVerifier
