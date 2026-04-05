import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

