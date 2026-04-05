import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

variable [IsScalarTower S A A] [SMulCommClass S A A]

variable [IsScalarTower R S A]

theorem apply_mem (h : QuasispectrumRestricts a f) {s : S} (hs : s ∈ quasispectrum S a) :
    f s ∈ quasispectrum R a := QuasispectrumRestricts.image h ▸ ⟨s, hs, rfl⟩

