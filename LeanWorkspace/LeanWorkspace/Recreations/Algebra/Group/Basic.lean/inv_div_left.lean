import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

