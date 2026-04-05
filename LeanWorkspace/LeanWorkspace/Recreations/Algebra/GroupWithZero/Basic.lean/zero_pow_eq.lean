import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem zero_pow_eq (n : ℕ) : (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zero]
  · rw [zero_pow h]

