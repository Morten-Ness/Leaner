import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K (-n₂)) (z₃ : CochainComplex.HomComplex.Cochain K L n₂) (h₁₂ : n₁ + (-n₂) = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃
      (show n₁₂ + n₂ = n₁ by rw [← h₁₂, add_assoc, neg_add_cancel, add_zero]) =
      z₁.comp (z₂.comp z₃ (neg_add_cancel n₂)) (add_zero n₁) := CochainComplex.HomComplex.Cochain.comp_assoc _ _ _ _ _ (by lia)

