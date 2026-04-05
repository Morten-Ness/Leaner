import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_comp_zero_cocycle {n : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n) (z₂ : CochainComplex.HomComplex.Cocycle G K 0) (m : ℤ) :
    CochainComplex.HomComplex.δ n m (z₁.comp z₂.1 (add_zero n)) =
      (CochainComplex.HomComplex.δ n m z₁).comp z₂.1 (add_zero m) := by
  by_cases hnm : n + 1 = m
  · simp [CochainComplex.HomComplex.δ_comp_zero_cochain _ _ _ hnm]
  · simp [CochainComplex.HomComplex.δ_shape _ _ hnm]

