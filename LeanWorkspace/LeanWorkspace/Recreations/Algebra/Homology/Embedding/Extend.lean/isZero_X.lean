import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem isZero_X {i : Option ι} (hi : i = none) :
    IsZero (HomologicalComplex.extend.X K i) := by
  subst hi
  exact Limits.isZero_zero _

