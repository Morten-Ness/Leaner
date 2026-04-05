import Mathlib

variable {M : Type*}

theorem associated_unit_mul_right {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u) :
    Associated a (u * a) := Associated.symm (associated_unit_mul_left a u hu)

