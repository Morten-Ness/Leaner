import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrum.nonempty [Nontrivial R] (a : A) : (quasispectrum R a).Nonempty := Set.nonempty_of_mem <| quasispectrum.zero_mem R a

