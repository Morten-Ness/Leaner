import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem eq_mul_of_inv_mul_eq₀ (hc : c ≠ 0) (h : b⁻¹ * a = c) : a = b * c := (mul_eq_of_eq_inv_mul₀ hc h.symm).symm

