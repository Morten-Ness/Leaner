import Mathlib

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 := inv_mul_cancel₀ (Invertible.ne_zero a)

