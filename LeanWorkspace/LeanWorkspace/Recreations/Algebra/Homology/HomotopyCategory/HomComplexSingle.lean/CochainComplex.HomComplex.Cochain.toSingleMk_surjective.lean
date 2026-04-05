import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem toSingleMk_surjective {q n : ℤ} (α : CochainComplex.HomComplex.Cochain K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) :
    ∃ (f : K.X p ⟶ X), CochainComplex.HomComplex.Cochain.toSingleMk f h = α := (CochainComplex.HomComplex.Cochain.toSingleEquiv h).symm.surjective α

