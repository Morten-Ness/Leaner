import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem quasispectrumRestricts_iff
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) :
    QuasispectrumRestricts a f ↔ (quasispectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) := ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

