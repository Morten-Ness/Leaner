import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv := rfl

