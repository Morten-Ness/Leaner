import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    CochainComplex.HomComplex.Cocycle.fromSingleMk (f + g) h q' hq' (by simp [hf, hg]) =
      CochainComplex.HomComplex.Cocycle.fromSingleMk f h q' hq' hf + CochainComplex.HomComplex.Cocycle.fromSingleMk g h q' hq' hg := by
  cat_disch

