import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_surjective {p n : ℤ} (α : CochainComplex.HomComplex.Cochain ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) :
    ∃ (f : X ⟶ K.X q), CochainComplex.HomComplex.Cochain.fromSingleMk f h = α := (CochainComplex.HomComplex.Cochain.fromSingleEquiv h).symm.surjective α

