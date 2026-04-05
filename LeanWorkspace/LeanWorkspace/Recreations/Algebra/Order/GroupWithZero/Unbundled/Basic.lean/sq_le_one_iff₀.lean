import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [ZeroLEOneClass M₀]

theorem sq_le_one_iff₀ (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 := pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

