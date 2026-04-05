import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_zero (x : M) : x ^ 0 = 1 := NatPowAssoc.npow_zero x

