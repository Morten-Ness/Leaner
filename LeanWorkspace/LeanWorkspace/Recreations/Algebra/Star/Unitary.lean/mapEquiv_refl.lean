import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem mapEquiv_refl : Unitary.mapEquiv (.refl R) = .refl (unitary R) := rfl

