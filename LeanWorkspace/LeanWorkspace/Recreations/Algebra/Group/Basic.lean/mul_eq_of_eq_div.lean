import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

