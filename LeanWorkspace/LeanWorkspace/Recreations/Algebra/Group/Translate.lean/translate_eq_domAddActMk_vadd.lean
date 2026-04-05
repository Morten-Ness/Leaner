import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_eq_domAddActMk_vadd (a : G) (f : G → α) : τ a f = DomAddAct.mk (-a) +ᵥ f := by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

