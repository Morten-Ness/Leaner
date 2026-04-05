import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

omit [IsKilling K L] [IsTriangularizable K H L] [CharZero K] in
theorem _root_.LieSubalgebra.isNonZero_coe_root (α : H.root) : (α : Weight K H L).IsNonZero := by
  aesop

