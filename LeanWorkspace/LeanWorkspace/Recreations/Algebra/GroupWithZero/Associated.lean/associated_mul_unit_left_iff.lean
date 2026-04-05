import Mathlib

variable {M : Type*}

theorem associated_mul_unit_left_iff {N : Type*} [Monoid N] {a b : N} {u : Units N} :
    Associated (a * u) b ↔ Associated a b := associated_mul_isUnit_left_iff u.isUnit

