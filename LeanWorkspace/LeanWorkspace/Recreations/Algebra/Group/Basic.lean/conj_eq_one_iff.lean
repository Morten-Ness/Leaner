import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one, mul_eq_left]

