import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem lieIdeal_eq_inf_cartan_sup_biSup_rootSpace (I : LieIdeal K L) :
    I.restr H = (I.restr H ⊓ H.toLieSubmodule) ⊔
      ⨆ (α : H.root) (_ : rootSpace H α.val ≤ I.restr H), rootSpace H α.val := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ hα ↦ hα))
  conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace]
  refine sup_le_sup_left (iSup₂_le fun α hα ↦ ?_) _
  by_cases h : rootSpace H α ≤ I.restr H
  · exact le_iSup₂_of_le ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩ h inf_le_right
  · have ha := Submodule.isAtom_iff_finrank_eq_one.mpr (LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα)
    have : I.restr H ⊓ rootSpace H (α : H → K) = ⊥ :=
      LieSubmodule.toSubmodule_injective ((ha.not_le_iff_disjoint.mp h).symm.eq_bot)
    simp only [this, bot_le]

