import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [ZeroLEOneClass M₀]

theorem one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a := one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

