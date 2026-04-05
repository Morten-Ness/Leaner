import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

variable [IsScalarTower R S A]

theorem algebraMap_image (h : SpectrumRestricts a f) :
    algebraMap R S '' spectrum R a = spectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [spectrum.preimage_algebraMap] using
      (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((SpectrumRestricts.rightInvOn h hs).symm ▸ hs), SpectrumRestricts.rightInvOn h hs⟩

