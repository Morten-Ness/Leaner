import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem mem_quasispectrum_iff {R A : Type*} [Semifield R] [Ring A]
    [Algebra R A] {a : A} {x : R} :
    x ∈ quasispectrum R a ↔ x = 0 ∨ x ∈ spectrum R a := by
  simp [quasispectrum_eq_spectrum_union_zero]

