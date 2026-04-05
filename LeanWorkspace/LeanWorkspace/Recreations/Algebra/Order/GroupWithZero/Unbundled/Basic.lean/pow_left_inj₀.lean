import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

theorem pow_left_inj₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b := (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

