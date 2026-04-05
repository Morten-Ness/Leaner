import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem one_div_div : 1 / (a / b) = b / a := by simp

