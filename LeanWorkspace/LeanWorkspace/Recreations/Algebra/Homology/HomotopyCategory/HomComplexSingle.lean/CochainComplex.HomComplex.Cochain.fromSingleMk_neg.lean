import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.fromSingleMk (-f) h = -CochainComplex.HomComplex.Cochain.fromSingleMk f h := (CochainComplex.HomComplex.Cochain.fromSingleEquiv h).symm.map_neg _

