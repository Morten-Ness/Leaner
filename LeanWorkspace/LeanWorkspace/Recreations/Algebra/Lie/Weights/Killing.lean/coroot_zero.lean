import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem coroot_zero [Nontrivial L] : LieAlgebra.IsKilling.coroot (0 : Weight K H L) = 0 := by simp [Weight.isZero_zero]

