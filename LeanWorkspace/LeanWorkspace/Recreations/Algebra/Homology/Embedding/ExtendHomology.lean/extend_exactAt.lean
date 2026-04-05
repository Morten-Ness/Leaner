import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extend_exactAt (j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    (K.extend e).ExactAt j' := exactAt_of_isSupported _ e j' hj'

