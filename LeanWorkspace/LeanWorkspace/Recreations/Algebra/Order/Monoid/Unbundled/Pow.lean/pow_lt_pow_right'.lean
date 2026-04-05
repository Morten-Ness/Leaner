import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftStrictMono M] {a : M} {n m : ℕ}

theorem pow_lt_pow_right' (ha : 1 < a) (h : n < m) : a ^ n < a ^ m := pow_right_strictMono' ha h

