import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) :
    CochainComplex.HomComplex.Cocycle.toSingleMk (0 : K.X p ⟶ X) h p' hp' (by simp) = 0 := by
  cat_disch

