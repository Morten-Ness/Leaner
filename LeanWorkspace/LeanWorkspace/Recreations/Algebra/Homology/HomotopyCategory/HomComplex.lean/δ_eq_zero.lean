import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_eq_zero {n : ℤ} (z : CochainComplex.HomComplex.Cocycle F G n) (m : ℤ) : CochainComplex.HomComplex.δ n m (z : CochainComplex.HomComplex.Cochain F G n) = 0 := by
  by_cases h : n + 1 = m
  · rw [← CochainComplex.HomComplex.Cocycle.mem_iff n m h]
    exact z.2
  · exact CochainComplex.HomComplex.δ_shape n m h _

