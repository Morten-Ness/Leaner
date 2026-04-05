import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem pow_mul_eq_zero_of_le {a b : M₀} {m n : ℕ} (hmn : m ≤ n)
    (h : a ^ m * b = 0) : a ^ n * b = 0 := by
  rw [show n = n - m + m by lia, pow_add, mul_assoc, h]
  simp

