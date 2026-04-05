import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K 0) (z₃ : CochainComplex.HomComplex.Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃) :
    (z₁.comp z₂ (add_zero n₁)).comp z₃ h₁₃ = z₁.comp (z₂.comp z₃ (zero_add n₃)) h₁₃ := CochainComplex.HomComplex.Cochain.comp_assoc _ _ _ _ _ (by lia)

