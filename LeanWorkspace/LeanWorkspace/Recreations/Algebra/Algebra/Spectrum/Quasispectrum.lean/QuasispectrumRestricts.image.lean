import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

variable [IsScalarTower S A A] [SMulCommClass S A A]

variable [IsScalarTower R S A]

theorem image (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispectrum R a := by
  simp only [← QuasispectrumRestricts.algebraMap_image h, Set.image_image, h.left_inv _, Set.image_id']

