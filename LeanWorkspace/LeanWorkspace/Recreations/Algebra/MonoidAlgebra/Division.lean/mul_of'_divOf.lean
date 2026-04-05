import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem mul_of'_divOf (x : k[G]) (a : G) : x * of' k G a /ᵒᶠ a = x := by
  ext
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, mul_single_apply_aux, mul_one]
  intro c hc
  rw [add_comm]
  exact add_right_inj _

