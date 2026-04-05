import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L] {α : Weight K H L}

theorem IsNonZero.neg (h : α.IsNonZero) : (-α).IsNonZero := fun e ↦ h (by simpa using e.neg)

