import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) {L : CochainComplex C ℤ}
    (g : K ⟶ L) :
    CochainComplex.HomComplex.Cocycle.fromSingleMk (f ≫ g.f q) h q' hq' (by simp [reassoc_of% hf]) =
      (CochainComplex.HomComplex.Cocycle.fromSingleMk f h q' hq' hf).postcomp g := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

