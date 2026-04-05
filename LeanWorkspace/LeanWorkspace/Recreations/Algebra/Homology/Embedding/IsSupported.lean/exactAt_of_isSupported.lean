import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    K.ExactAt i' := IsSupported.exactAt i' hi'

