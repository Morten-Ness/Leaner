import Mathlib

variable {M : Type*}

theorem associated_mul_unit_right_iff {N : Type*} [Monoid N] {a b : N} {u : Units N} :
    Associated a (b * u) ↔ Associated a b := associated_mul_isUnit_right_iff u.isUnit

