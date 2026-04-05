import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) :
    α (LieAlgebra.IsKilling.coroot α) = 2 := by
  rw [← Weight.coe_coe]
  simpa [LieAlgebra.IsKilling.coroot] using inv_mul_cancel₀ (LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero hα)

