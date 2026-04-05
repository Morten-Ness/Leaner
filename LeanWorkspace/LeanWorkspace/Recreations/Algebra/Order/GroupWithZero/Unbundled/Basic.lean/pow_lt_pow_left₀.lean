import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

theorem pow_lt_pow_left₀ [MulPosMono M₀] (hab : a < b)
    (ha : 0 ≤ a) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa using hab
  | n + 2, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_succ_pos (ha.trans_lt hab) _)
