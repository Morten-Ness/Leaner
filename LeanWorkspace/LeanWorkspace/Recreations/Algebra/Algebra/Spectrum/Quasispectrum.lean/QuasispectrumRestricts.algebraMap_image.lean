import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

variable [IsScalarTower S A A] [SMulCommClass S A A]

variable [IsScalarTower R S A]

theorem algebraMap_image (h : QuasispectrumRestricts a f) :
    algebraMap R S '' quasispectrum R a = quasispectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [quasispectrum.preimage_algebraMap] using
      (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

