import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

