import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.coe_zero [Nontrivial R] (a : A) : (0 : quasispectrum R a) = (0 : R) := rfl

