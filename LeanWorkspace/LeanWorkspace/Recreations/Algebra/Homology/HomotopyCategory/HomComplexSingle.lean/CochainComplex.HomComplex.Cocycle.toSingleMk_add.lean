import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    CochainComplex.HomComplex.Cocycle.toSingleMk (f + g) h p' hp' (by simp [hf, hg]) =
      CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf + CochainComplex.HomComplex.Cocycle.toSingleMk g h p' hp' hg := by
  cat_disch

