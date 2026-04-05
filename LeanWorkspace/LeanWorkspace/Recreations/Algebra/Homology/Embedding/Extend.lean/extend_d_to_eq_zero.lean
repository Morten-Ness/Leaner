import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact HomologicalComplex.extend.d_none_eq_zero HomologicalComplex.extend _ _ _ hi'
  · rw [HomologicalComplex.extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

