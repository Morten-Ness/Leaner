import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv, eq_comm]

