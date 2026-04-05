import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : K ⟶ L) :
    CochainComplex.HomComplex.Cochain.fromSingleMk (f ≫ g.f q) h =
      (CochainComplex.HomComplex.Cochain.fromSingleMk f h).comp (.ofHom g) (add_zero n) := (CochainComplex.HomComplex.Cochain.fromSingleEquiv h).injective (by simp [CochainComplex.HomComplex.Cochain.fromSingleEquiv, singleFunctor, singleFunctors])

