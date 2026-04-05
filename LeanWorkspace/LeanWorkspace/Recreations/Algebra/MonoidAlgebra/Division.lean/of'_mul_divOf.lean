import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem of'_mul_divOf (a : G) (x : k[G]) : of' k G a * x /ᵒᶠ a = x := by
  ext
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, single_mul_apply_aux, one_mul]
  intro c hc
  exact add_right_inj _

