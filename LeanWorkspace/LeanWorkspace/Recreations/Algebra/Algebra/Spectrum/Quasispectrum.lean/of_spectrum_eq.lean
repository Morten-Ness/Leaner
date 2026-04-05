import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem of_spectrum_eq {a b : A} {f : S → R} (ha : SpectrumRestricts a f)
    (h : spectrum S a = spectrum S b) : SpectrumRestricts b f where
  SpectrumRestricts.rightInvOn := by
    rw [quasispectrum_eq_spectrum_union_zero, ← h, ← quasispectrum_eq_spectrum_union_zero]
    exact QuasispectrumRestricts.rightInvOn ha
  left_inv := ha.left_inv

