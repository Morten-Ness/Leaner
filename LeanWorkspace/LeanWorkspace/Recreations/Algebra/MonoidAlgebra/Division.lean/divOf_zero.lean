import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x := by
  ext
  simp only [AddMonoidAlgebra.divOf_apply, zero_add]

