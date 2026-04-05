import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [MulPosMono M₀]

theorem sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b := pow_lt_pow_iff_left₀ ha hb two_ne_zero

