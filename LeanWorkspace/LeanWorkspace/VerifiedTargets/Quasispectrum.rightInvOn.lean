import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem rightInvOn (h : SpectrumRestricts a f) : (spectrum S a).RightInvOn f (algebraMap R S) := (QuasispectrumRestricts.rightInvOn h).mono <| spectrum_subset_quasispectrum _ _

