import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem fromSingleMk_v {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    (CochainComplex.HomComplex.Cochain.fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f := by
  simp [CochainComplex.HomComplex.Cochain.fromSingleMk]

