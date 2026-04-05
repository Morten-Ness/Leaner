import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.not_isUnit_mem (a : A) {r : R} (hr : ¬ IsUnit r) : r ∈ quasispectrum R a := fun hr' ↦ (hr hr').elim

