import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zero_zpow : ∀ n : ℤ, n ≠ 0 → (0 : G₀) ^ n = 0
  | (n : ℕ), h => by rw [zpow_natCast, zero_pow]; simpa [Int.natCast_eq_zero] using h
  | .negSucc n, _ => by simp
