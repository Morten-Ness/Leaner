import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftMono M] [MulRightMono M]

theorem lt_of_pow_lt_pow_left' {a b : M} (n : ℕ) : a ^ n < b ^ n → a < b := (pow_left_mono _).reflect_lt

