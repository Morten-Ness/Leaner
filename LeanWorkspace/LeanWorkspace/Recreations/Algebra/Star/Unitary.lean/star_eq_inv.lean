import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem star_eq_inv (U : unitary R) : star U = U⁻¹ := rfl

