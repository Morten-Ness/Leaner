import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero (K.X i') := IsStrictlySupported.isZero i' hi'

