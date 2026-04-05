import Mathlib

variable {R A : Type*}

variable [Ring R] [StarRing R]

theorem val_pow (x : selfAdjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n := rfl

