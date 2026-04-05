import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_zero_cocycle_comp {n : ℤ} (z₁ : CochainComplex.HomComplex.Cocycle F G 0) (z₂ : CochainComplex.HomComplex.Cochain G K n) (m : ℤ) :
    CochainComplex.HomComplex.δ n m (z₁.1.comp z₂ (zero_add n)) =
      z₁.1.comp (CochainComplex.HomComplex.δ n m z₂) (zero_add m) := by
  by_cases hnm : n + 1 = m
  · simp [CochainComplex.HomComplex.δ_zero_cochain_comp _ _ _ hnm]
  · simp [CochainComplex.HomComplex.δ_shape _ _ hnm]

