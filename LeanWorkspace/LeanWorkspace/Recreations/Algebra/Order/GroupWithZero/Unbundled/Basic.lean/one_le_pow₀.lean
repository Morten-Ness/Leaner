import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) {n : ℕ} : 1 ≤ a ^ n := pow_zero a ▸ pow_right_mono₀ ha n.zero_le

