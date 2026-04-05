import Mathlib

variable {M : Type*}

theorem associated_mul_isUnit_right_iff {N : Type*} [Monoid N] {a b u : N} (hu : IsUnit u) :
    Associated a (b * u) ↔ Associated a b := Associated.Associated.trans Associated.comm <| Associated.trans (associated_mul_isUnit_left_iff hu) Associated.comm

