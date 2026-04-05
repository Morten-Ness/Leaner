import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem sl2SubmoduleOfRoot_ne_bot (α : Weight K H L) (hα : α.IsNonZero) :
    LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα ≠ ⊥ := by
  rw [LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup]
  exact ne_bot_of_le_ne_bot α.genWeightSpace_ne_bot (le_sup_of_le_left le_sup_left)

