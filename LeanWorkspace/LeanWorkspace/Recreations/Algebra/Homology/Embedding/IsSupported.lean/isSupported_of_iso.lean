import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

include e' in
theorem isSupported_of_iso [K.IsSupported e] : L.IsSupported e where
  exactAt i' hi' := (K.exactAt_of_isSupported e i' hi').of_iso e'

