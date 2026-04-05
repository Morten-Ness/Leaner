import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.zero_mem [Nontrivial R] (a : A) : 0 ∈ quasispectrum R a := quasispectrum.not_isUnit_mem a <| by simp

