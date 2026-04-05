import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

theorem isZero_stupidTrunc_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.stupidTrunc e).X i') := isZero_extend_X _ _ _ hi'

