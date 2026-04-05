import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem eq_mul_of_mul_inv_eq₀ (hb : b ≠ 0) (h : a * c⁻¹ = b) : a = b * c := (mul_eq_of_eq_mul_inv₀ hb h.symm).symm

