import Mathlib

variable {M : Type*}

theorem associated_isUnit_mul_right_iff {N : Type*} [CommMonoid N] {a u b : N} (hu : IsUnit u) :
    Associated a (u * b) ↔ Associated a b := Associated.Associated.trans Associated.comm <| Associated.trans (associated_isUnit_mul_left_iff hu) Associated.comm

