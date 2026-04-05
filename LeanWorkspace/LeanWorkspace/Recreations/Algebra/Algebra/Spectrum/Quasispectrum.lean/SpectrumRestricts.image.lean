import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

variable [IsScalarTower R S A]

theorem image (h : SpectrumRestricts a f) : f '' spectrum S a = spectrum R a := by
  simp only [← SpectrumRestricts.algebraMap_image h, Set.image_image, h.left_inv _, Set.image_id']

