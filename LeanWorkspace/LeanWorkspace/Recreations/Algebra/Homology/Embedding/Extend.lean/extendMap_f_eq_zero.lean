import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
theorem extendMap_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (HomologicalComplex.extendMap φ e).f i' = 0 := by
  dsimp [HomologicalComplex.extendMap]
  rw [HomologicalComplex.extend.mapX_none HomologicalComplex.extend φ (e.r_eq_none i' hi')]

