import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem reflectionPerm_mem_rootSet_iff (I : LieIdeal K L) (α β : H.root) :
    (rootSystem H).reflectionPerm β α ∈ I.rootSet ↔ α ∈ I.rootSet := by
  let S := rootSystem H
  suffices h : ∀ γ δ : H.root, δ ∈ I.rootSet → S.reflectionPerm γ δ ∈ I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [LieIdeal.mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := I.rootSpace_le_of_apply_coroot_ne_zero hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ ≠ 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact I.rootSpace_le_of_apply_coroot_ne_zero hγ h_neg

