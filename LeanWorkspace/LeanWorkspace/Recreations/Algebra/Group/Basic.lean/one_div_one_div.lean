import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem one_div_one_div : 1 / (1 / a) = a := by simp

