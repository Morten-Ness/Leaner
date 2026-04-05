import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

theorem quasiIsoAt_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    QuasiIsoAt (K.shortComplexTruncLE e).g i' := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact K.isIso_homologyMap_shortComplexTruncLE_g e i' hi'

