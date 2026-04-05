import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem toSingleMk_v {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    (CochainComplex.HomComplex.Cochain.toSingleMk f h).v p q h =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv := by
  simp [CochainComplex.HomComplex.Cochain.toSingleMk]

