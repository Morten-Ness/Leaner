import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.toSingleMk (-f) h = -CochainComplex.HomComplex.Cochain.toSingleMk f h := (CochainComplex.HomComplex.Cochain.toSingleEquiv h).symm.map_neg _

