import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem toSingleMk_postcomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) {X' : C} (g : X ⟶ X') :
    CochainComplex.HomComplex.Cochain.toSingleMk (f ≫ g) h =
      (CochainComplex.HomComplex.Cochain.toSingleMk f h).comp (.ofHom ((singleFunctor C q).map g)) (add_zero n) := by
  apply (CochainComplex.HomComplex.Cochain.toSingleEquiv h).injective
  simp [CochainComplex.HomComplex.Cochain.toSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

