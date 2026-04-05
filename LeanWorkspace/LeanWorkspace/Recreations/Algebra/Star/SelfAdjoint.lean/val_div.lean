import Mathlib

variable {R A : Type*}

variable [Field R] [StarRing R]

theorem val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) := rfl

