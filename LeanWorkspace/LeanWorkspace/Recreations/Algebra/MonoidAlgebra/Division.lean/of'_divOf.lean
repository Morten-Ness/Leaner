import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using AddMonoidAlgebra.mul_of'_divOf (1 : k[G]) a

