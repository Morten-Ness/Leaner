import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem fromSingleMk_precomp
    {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    CochainComplex.HomComplex.Cochain.fromSingleMk (g ≫ f) h =
      (CochainComplex.HomComplex.Cochain.ofHom ((singleFunctor C p).map g)).comp (CochainComplex.HomComplex.Cochain.fromSingleMk f h) (zero_add n) := by
  apply (CochainComplex.HomComplex.Cochain.fromSingleEquiv h).injective
  simp [CochainComplex.HomComplex.Cochain.fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

