import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by lia), zero_mul]
  · exact pow_sub₀ _ ha <| Nat.le_of_lt h

