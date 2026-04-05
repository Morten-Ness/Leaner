import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

variable [IsScalarTower R S A]

theorem apply_mem (h : SpectrumRestricts a f) {s : S} (hs : s ∈ spectrum S a) :
    f s ∈ spectrum R a := SpectrumRestricts.image h ▸ ⟨s, hs, rfl⟩

