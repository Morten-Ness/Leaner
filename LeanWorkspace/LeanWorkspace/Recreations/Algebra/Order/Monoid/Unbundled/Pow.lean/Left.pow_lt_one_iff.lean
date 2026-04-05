import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

theorem Left.pow_lt_one_iff [MulLeftStrictMono M] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 := Left.pow_lt_one_iff' hn

