import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem toSingleMk_precomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : L ⟶ K) :
    CochainComplex.HomComplex.Cochain.toSingleMk (g.f p ≫ f) h =
      (CochainComplex.HomComplex.Cochain.ofHom g).comp (CochainComplex.HomComplex.Cochain.toSingleMk f h) (zero_add n) := (CochainComplex.HomComplex.Cochain.toSingleEquiv h).injective (by simp [CochainComplex.HomComplex.Cochain.toSingleEquiv, singleFunctor, singleFunctors])

