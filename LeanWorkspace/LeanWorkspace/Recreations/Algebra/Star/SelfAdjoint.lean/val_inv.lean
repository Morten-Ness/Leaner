import Mathlib

variable {R A : Type*}

variable [Field R] [StarRing R]

theorem val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ := rfl

