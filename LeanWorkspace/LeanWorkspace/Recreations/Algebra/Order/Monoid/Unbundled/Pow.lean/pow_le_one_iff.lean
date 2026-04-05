import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftMono M]

theorem pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 := one_le_pow_iff (M := Mᵒᵈ) hn

