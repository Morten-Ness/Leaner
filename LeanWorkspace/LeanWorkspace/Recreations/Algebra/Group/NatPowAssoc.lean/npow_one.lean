import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_one (x : M) : x ^ 1 = x := NatPowAssoc.npow_one x

