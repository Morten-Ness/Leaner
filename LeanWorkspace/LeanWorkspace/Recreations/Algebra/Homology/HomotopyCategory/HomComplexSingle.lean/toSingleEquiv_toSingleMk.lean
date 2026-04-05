import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem toSingleEquiv_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.toSingleEquiv h (CochainComplex.HomComplex.Cochain.toSingleMk f h) = f := by
  simp [CochainComplex.HomComplex.Cochain.toSingleEquiv]

