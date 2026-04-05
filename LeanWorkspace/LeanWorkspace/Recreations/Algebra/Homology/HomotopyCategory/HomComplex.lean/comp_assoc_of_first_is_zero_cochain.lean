import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G 0) (z₂ : CochainComplex.HomComplex.Cochain G K n₂) (z₃ : CochainComplex.HomComplex.Cochain K L n₃)
    (h₂₃ : n₂ + n₃ = n₂₃) :
    (z₁.comp z₂ (zero_add n₂)).comp z₃ h₂₃ = z₁.comp (z₂.comp z₃ h₂₃) (zero_add n₂₃) := CochainComplex.HomComplex.Cochain.comp_assoc _ _ _ _ _ (by lia)

