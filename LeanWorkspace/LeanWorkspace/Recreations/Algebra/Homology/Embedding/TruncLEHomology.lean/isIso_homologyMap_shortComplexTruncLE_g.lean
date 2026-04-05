import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

theorem isIso_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsIso (homologyMap (K.shortComplexTruncLE e).g i') := by
  have := K.mono_homologyMap_shortComplexTruncLE_g e i' hi'
  apply isIso_of_mono_of_epi

