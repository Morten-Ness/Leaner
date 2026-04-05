import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M} {n : ℕ}

theorem one_lt_pow' (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k := pow_lt_one' (M := Mᵒᵈ) ha hk

