import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_postcomp {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {X' : C} (g : X ⟶ X') :
    CochainComplex.HomComplex.Cocycle.toSingleMk (f ≫ g) h p' hp' (by simp [reassoc_of% hf]) =
      (CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf).postcomp ((singleFunctor C q).map g) := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_postcomp])

