import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

variable [ZeroLEOneClass M₀]

theorem lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

