import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K n₂) (z₃ : CochainComplex.HomComplex.Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃ (add_zero n₁₂) = z₁.comp (z₂.comp z₃ (add_zero n₂)) h₁₂ := CochainComplex.HomComplex.Cochain.comp_assoc _ _ _ _ _ (by lia)

