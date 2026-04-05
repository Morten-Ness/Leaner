import Mathlib

variable {α : Type*}

theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]

