import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (b * c) = a * c := by
  rw [mul_assoc, ← mul_assoc b⁻¹, inv_mul_cancel, one_mul]

