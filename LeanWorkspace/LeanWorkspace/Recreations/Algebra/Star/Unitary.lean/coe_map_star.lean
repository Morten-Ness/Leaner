import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem coe_map_star (f : R →⋆* S) (x : unitary R) : Unitary.map f (star x) = f (star x) := rfl

