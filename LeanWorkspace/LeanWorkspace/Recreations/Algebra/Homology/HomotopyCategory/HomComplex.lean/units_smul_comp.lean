import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem units_smul_comp {n₁ n₂ n₁₂ : ℤ} (k : Rˣ) (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h) := by
  apply CochainComplex.HomComplex.Cochain.smul_comp

