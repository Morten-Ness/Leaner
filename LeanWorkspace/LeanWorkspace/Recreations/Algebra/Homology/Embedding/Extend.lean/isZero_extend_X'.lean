import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') := HomologicalComplex.extend.isZero_X HomologicalComplex.extend K hi'

