import Mathlib

variable {R A : Type*}

variable [NonUnitalCommRing R] [StarRing R]

theorem val_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y := rfl

