import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

