import Mathlib

variable {M : Type*}

theorem associated_unit_mul_left_iff {N : Type*} [CommMonoid N] {a b : N} {u : Units N} :
    Associated (↑u * a) b ↔ Associated a b := associated_isUnit_mul_left_iff u.isUnit

