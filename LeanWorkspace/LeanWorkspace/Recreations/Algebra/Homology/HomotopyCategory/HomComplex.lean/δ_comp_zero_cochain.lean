import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_comp_zero_cochain {n₁ : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) :
    CochainComplex.HomComplex.δ n₁ m₁ (z₁.comp z₂ (add_zero n₁)) =
      z₁.comp (CochainComplex.HomComplex.δ 0 1 z₂) h₁ + (CochainComplex.HomComplex.δ n₁ m₁ z₁).comp z₂ (add_zero m₁) := by
  simp only [CochainComplex.HomComplex.δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_smul,
    Int.negOnePow_zero]

