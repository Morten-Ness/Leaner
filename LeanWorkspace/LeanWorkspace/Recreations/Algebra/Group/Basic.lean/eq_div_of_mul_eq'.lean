import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

