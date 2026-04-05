import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

theorem pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n ≠ 0) :
    StrictMonoOn (· ^ n : M₀ → M₀) {a | 0 ≤ a} := fun _a ha _b _ hab ↦ pow_lt_pow_left₀ hab ha hn

