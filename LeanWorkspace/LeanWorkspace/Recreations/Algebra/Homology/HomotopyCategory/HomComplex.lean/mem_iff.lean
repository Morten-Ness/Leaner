import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem mem_iff (hnm : n + 1 = m) (z : CochainComplex.HomComplex.Cochain F G n) :
    z ∈ CochainComplex.HomComplex.cocycle F G n ↔ CochainComplex.HomComplex.δ n m z = 0 := by subst hnm; rfl

