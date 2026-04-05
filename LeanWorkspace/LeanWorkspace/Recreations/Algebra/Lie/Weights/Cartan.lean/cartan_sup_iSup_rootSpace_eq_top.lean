import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

variable {K : Type*} [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [LieModule.IsTriangularizable K H L]

theorem cartan_sup_iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), rootSpace H α = ⊤ := by
  rw [eq_top_iff, ← LieModule.iSup_genWeightSpace_eq_top', iSup_le_iff]
  intro α
  by_cases hα : α.IsZero
  · simp [hα]
  · exact le_sup_of_le_right <| le_iSup₂_of_le α hα (le_refl _)

