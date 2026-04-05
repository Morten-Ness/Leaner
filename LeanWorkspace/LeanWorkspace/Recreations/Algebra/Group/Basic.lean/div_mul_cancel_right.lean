import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel_right]

