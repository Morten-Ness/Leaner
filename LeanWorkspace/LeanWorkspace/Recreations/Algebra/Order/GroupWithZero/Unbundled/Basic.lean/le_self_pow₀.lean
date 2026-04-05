import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa only [pow_one] using pow_le_pow_right₀ ha <| Nat.pos_iff_ne_zero.2 hn

