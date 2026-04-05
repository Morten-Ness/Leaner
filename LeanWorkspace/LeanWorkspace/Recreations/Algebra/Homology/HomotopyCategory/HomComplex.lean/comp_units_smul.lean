import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_units_smul {n₁ n₂ n₁₂ : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (k : Rˣ) (z₂ : CochainComplex.HomComplex.Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h) := by
  apply CochainComplex.HomComplex.Cochain.comp_smul

