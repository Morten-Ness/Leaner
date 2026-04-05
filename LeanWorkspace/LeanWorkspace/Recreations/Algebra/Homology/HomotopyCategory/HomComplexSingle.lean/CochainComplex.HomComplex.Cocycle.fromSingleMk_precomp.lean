import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    CochainComplex.HomComplex.Cocycle.fromSingleMk (g ≫ f) h q' hq' (by simp [hf]) =
      (CochainComplex.HomComplex.Cocycle.fromSingleMk f h q' hq' hf).precomp ((singleFunctor C p).map g) := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])

