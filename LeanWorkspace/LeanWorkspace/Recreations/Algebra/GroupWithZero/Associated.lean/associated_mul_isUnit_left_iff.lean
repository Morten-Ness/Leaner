import Mathlib

variable {M : Type*}

theorem associated_mul_isUnit_left_iff {N : Type*} [Monoid N] {a u b : N} (hu : IsUnit u) :
    Associated (a * u) b ↔ Associated a b := ⟨Associated.trans (associated_mul_unit_right _ _ hu), Associated.trans (associated_mul_unit_left _ _ hu)⟩

