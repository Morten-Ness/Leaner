import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.toSingleMk (f + g) h = CochainComplex.HomComplex.Cochain.toSingleMk f h + CochainComplex.HomComplex.Cochain.toSingleMk g h := (CochainComplex.HomComplex.Cochain.toSingleEquiv h).symm.map_add _ _

