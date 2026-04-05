import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 := mul_inv_cancel₀ (Invertible.ne_zero a)

