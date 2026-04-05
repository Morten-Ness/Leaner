import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') :
    CochainComplex.HomComplex.Cocycle.fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0 := by
  cat_disch

