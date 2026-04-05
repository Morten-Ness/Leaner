import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrumRestricts_iff_spectrumRestricts {R S A : Type*} [Semifield R] [Semifield S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts a f := by rfl

