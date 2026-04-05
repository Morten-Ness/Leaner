import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem mul_comm_iff {R S A : Type*} [Semifield R] [Field S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] {a b : A} {f : S → R} :
    SpectrumRestricts (a * b) f ↔ SpectrumRestricts (b * a) f := QuasispectrumRestricts.mul_comm_iff

alias ⟨mul_comm, _⟩ := QuasispectrumRestricts.mul_comm_iff

