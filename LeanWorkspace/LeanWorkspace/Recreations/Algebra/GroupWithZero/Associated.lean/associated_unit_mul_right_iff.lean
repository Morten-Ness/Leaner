import Mathlib

variable {M : Type*}

theorem associated_unit_mul_right_iff {N : Type*} [CommMonoid N] {a b : N} {u : Units N} :
    Associated a (↑u * b) ↔ Associated a b := associated_isUnit_mul_right_iff u.isUnit

