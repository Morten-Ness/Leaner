import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem _root_.spectrumRestricts_iff :
    SpectrumRestricts a f ↔ (spectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) := ⟨fun h ↦ ⟨SpectrumRestricts.rightInvOn h, h.left_inv⟩, fun h ↦ .of_rightInvOn h.2 h.1⟩

