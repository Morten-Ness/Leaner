import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum_eq_spectrum_union_zero (R : Type*) {A : Type*} [Semifield R] [Ring A]
    [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {0} := by
  convert quasispectrum_eq_spectrum_union R a
  simp

