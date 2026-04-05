import Mathlib

variable {K L M : Type*}

variable [Field K] [LieRing L] [LieAlgebra K L]

variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]

variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)

variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)

variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)

theorem atomistic : ∀ I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J ≤ I} = I := by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := (eq_bot_or_exists_atom_le I).resolve_left hI
  let J' := LieAlgebra.InvariantForm.orthogonal Φ hΦ_inv J
  suffices I ≤ J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.setOf_subset_setOf, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (LieAlgebra.InvariantForm.orthogonal_isCompl Φ hΦ_nondeg hΦ_inv hΦ_refl hL J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I ≤ J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact LieAlgebra.InvariantForm.orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL J hJ le_rfl (hJI.trans hIJ')

