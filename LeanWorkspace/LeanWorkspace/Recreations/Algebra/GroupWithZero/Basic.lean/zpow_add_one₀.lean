import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zpow_add_one₀ (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [ha]
  | .negSucc (n + 1) => by
    rw [Int.negSucc_eq, zpow_neg, Int.neg_add, Int.neg_add_cancel_right, zpow_neg,
      ← Int.natCast_succ, zpow_natCast, zpow_natCast, pow_succ' _ (n + 1), mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ ha, mul_one]
