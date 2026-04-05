import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftStrictMono M] {a : M} {m n : ℕ}

theorem pow_le_pow_iff_right' (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (pow_right_strictMono' ha).le_iff_le

