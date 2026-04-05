import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem zero_pow_eq_zero [Nontrivial M₀] : (0 : M₀) ^ n = 0 ↔ n ≠ 0 := ⟨by rintro h rfl; simp at h, zero_pow⟩

