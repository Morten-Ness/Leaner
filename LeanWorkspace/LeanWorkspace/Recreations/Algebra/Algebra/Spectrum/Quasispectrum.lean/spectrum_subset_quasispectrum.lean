import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem spectrum_subset_quasispectrum (R : Type*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    (a : A) : spectrum R a ⊆ quasispectrum R a := quasispectrum_eq_spectrum_union R a ▸ Set.subset_union_left

