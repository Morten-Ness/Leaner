import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem fromSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [CochainComplex.HomComplex.Cochain.fromSingleMk]

