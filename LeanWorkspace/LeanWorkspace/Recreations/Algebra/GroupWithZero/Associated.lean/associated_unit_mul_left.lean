import Mathlib

variable {M : Type*}

theorem associated_unit_mul_left {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u) :
    Associated (u * a) a := by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu

