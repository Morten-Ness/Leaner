import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

variable {K : Type*} [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [LieModule.IsTriangularizable K H L]

theorem lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) :
    I.restr H = (I.restr H ⊓ H.toLieSubmodule) ⊔
      ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), I.restr H ⊓ rootSpace H α := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ _ ↦ inf_le_left))
  conv_lhs => rw [LieAlgebra.lieIdeal_eq_iSup_inf_genWeightSpace]
  exact iSup_le fun α ↦ by
    by_cases hα : α.IsZero
    · rw [show genWeightSpace L (α : H → K) = H.toLieSubmodule from by ext; simp [hα.eq]]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)

