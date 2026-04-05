import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftStrictMono M] [MulRightStrictMono M] {f : β → M} {n : ℕ}

theorem pow_lt_pow_left' (hn : n ≠ 0) {a b : M} (hab : a < b) : a ^ n < b ^ n := pow_left_strictMono hn hab

