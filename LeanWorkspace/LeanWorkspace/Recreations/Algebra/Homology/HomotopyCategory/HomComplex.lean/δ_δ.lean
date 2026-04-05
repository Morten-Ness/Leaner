import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_δ (n₀ n₁ n₂ : ℤ) (z : CochainComplex.HomComplex.Cochain F G n₀) : CochainComplex.HomComplex.δ n₁ n₂ (CochainComplex.HomComplex.δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [CochainComplex.HomComplex.δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [CochainComplex.HomComplex.δ_shape _ _ h₀₁, δ_zero]
  ext p q hpq
  dsimp
  simp only [CochainComplex.HomComplex.δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    CochainComplex.HomComplex.δ_v n₀ n₁ h₀₁ z p (q - 1) (by lia) (q - 2) _ (by lia) rfl,
    CochainComplex.HomComplex.δ_v n₀ n₁ h₀₁ z (p + 1) q (by lia) _ (p + 2) rfl (by lia),
    ← h₁₂, Int.negOnePow_succ, add_comp, assoc,
    HomologicalComplex.d_comp_d, comp_zero, zero_add, comp_add,
    HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero,
    add_zero, add_neg_cancel, Units.neg_smul,
    Linear.units_smul_comp, Linear.comp_units_smul]

