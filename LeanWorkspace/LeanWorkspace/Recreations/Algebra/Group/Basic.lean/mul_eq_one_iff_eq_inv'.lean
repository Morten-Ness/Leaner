import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq, eq_comm]

