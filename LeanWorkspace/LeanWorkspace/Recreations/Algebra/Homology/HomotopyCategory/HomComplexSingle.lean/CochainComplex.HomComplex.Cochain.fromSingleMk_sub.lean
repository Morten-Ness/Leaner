import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.fromSingleMk (f - g) h = CochainComplex.HomComplex.Cochain.fromSingleMk f h - CochainComplex.HomComplex.Cochain.fromSingleMk g h := (CochainComplex.HomComplex.Cochain.fromSingleEquiv h).symm.map_sub _ _

