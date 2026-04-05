import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹ := invOf_eq_right_inv (mul_inv_cancel₀ (Invertible.ne_zero a))

