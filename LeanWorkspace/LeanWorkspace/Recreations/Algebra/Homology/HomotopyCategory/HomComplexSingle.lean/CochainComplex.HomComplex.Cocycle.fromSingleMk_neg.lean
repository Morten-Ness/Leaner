import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    CochainComplex.HomComplex.Cocycle.fromSingleMk (-f) h q' hq' (by simp [hf]) = - CochainComplex.HomComplex.Cocycle.fromSingleMk f h q' hq' hf := by
  cat_disch

