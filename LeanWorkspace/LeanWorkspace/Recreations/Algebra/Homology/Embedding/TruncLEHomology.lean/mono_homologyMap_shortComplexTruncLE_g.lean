import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

theorem mono_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    Mono (homologyMap (K.shortComplexTruncLE e).g i') := ((K.shortComplexTruncLE_shortExact e).homology_exact₂ i').mono_g
    (by apply ((K.truncLE e).exactAt_of_isSupported e i' hi').isZero_homology.eq_of_src)

