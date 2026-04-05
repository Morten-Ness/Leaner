import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem disjoint_ker_weight_corootSpace (α : Weight K H L) :
    Disjoint α.ker (corootSpace α) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ ↦ ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact LieAlgebra.IsKilling.eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

