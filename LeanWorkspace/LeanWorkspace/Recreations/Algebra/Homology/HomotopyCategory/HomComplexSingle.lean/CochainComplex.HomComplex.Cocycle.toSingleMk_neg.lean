import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    CochainComplex.HomComplex.Cocycle.toSingleMk (-f) h p' hp' (by simp [hf]) =
      - CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf := by
  cat_disch

