import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

variable [IsScalarTower R S A]

theorem subset_preimage (h : SpectrumRestricts a f) : spectrum S a ⊆ f ⁻¹' spectrum R a := SpectrumRestricts.image h ▸ (spectrum S a).subset_preimage_image f

