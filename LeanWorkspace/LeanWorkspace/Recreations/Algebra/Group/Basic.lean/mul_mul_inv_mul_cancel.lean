import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻¹ * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul]

