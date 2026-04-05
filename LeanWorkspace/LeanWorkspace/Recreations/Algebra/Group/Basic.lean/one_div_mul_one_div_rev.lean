import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

