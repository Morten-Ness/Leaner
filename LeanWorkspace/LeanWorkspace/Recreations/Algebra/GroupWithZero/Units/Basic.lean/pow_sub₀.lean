import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

