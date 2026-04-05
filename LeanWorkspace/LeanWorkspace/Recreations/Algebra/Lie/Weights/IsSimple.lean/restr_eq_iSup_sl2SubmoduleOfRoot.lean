import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem restr_eq_iSup_sl2SubmoduleOfRoot (I : LieIdeal K L) :
    I.restr H =
      ⨆ (α : H.root) (_ : α ∈ I.rootSet), sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
  apply le_antisymm
  · rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, LieIdeal.restr_inf_cartan_eq_biSup_corootSubmodule]
    apply sup_le
    · exact iSup₂_le fun β hβ ↦ le_iSup₂_of_le β hβ
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα ↦ le_iSup₂_of_le α hα
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)
  · exact iSup₂_le fun α hα ↦ by
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact hα
      · apply I.rootSpace_le_of_apply_coroot_ne_zero hα
        simp [Pi.neg_apply, root_apply_coroot (H.isNonZero_coe_root α)]
      · exact I.corootSubmodule_le hα

