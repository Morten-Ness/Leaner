import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem d_none_eq_zero (i j : Option ι) (hi : i = none) :
    HomologicalComplex.extend.d K i j = 0 := by subst hi; rfl

