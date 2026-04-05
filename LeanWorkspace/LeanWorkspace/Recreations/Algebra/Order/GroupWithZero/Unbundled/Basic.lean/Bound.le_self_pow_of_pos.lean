import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : 0 < n) :
    a ≤ a ^ n := le_self_pow₀ ha hn.ne'

