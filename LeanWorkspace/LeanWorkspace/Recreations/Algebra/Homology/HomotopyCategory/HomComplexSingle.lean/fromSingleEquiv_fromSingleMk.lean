import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleEquiv_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.fromSingleEquiv h (CochainComplex.HomComplex.Cochain.fromSingleMk f h) = f := by
  simp [CochainComplex.HomComplex.Cochain.fromSingleEquiv]

