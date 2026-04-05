import Mathlib

variable {R A : Type*}

variable [Field R] [StarRing R]

theorem val_zpow (x : selfAdjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z := rfl

