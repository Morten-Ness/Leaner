import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_add (k n : ℕ) (x : M) : x ^ (k + n) = x ^ k * x ^ n := NatPowAssoc.npow_add k n x

