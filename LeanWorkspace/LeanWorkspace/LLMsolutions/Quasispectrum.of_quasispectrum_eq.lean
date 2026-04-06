import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

theorem of_quasispectrum_eq {a b : A} {f : S → R} (ha : QuasispectrumRestricts a f)
    (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f where
  rightInvOn := by
    simpa [h] using ha.rightInvOn
  left_inv := ha.left_inv
