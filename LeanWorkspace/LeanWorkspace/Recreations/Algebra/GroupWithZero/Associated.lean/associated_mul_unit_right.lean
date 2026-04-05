import Mathlib

variable {M : Type*}

theorem associated_mul_unit_right {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u) :
    Associated a (a * u) := Associated.symm (associated_mul_unit_left a u hu)

