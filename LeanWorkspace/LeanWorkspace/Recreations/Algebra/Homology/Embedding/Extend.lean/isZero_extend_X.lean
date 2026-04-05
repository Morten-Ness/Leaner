import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem isZero_extend_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.extend e).X i') := K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')

