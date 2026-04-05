import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

theorem mem_rootSet {I : LieIdeal K L} {α : H.root} :
    α ∈ I.rootSet ↔ rootSpace H α.1 ≤ I.restr H := Iff.rfl

