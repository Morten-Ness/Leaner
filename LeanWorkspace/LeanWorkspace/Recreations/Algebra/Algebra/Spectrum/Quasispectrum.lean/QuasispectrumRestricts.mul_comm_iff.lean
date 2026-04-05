import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

variable [IsScalarTower S A A] [SMulCommClass S A A]

theorem mul_comm_iff {f : S → R} {a b : A} :
    QuasispectrumRestricts (a * b) f ↔ QuasispectrumRestricts (b * a) f := by
  simp only [quasispectrumRestricts_iff, quasispectrum.mul_comm]

alias ⟨mul_comm, _⟩ := mul_comm_iff

