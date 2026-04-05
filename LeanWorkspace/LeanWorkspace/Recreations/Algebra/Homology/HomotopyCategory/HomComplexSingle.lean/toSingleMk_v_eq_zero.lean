import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_v_eq_zero {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (CochainComplex.HomComplex.Cochain.toSingleMk f h).v p' q' hpq' = 0 := single_v_eq_zero _ _ _ _ _ hp'

