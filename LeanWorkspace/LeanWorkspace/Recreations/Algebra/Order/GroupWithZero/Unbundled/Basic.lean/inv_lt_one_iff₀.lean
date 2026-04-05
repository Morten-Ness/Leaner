import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable {m n : ℤ}

variable [PosMulStrictMono G₀]

variable [ZeroLEOneClass G₀]

theorem inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

