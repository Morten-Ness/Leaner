import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : spectrum S a ⊆ Set.range (algebraMap R S)) : SpectrumRestricts a f where
  SpectrumRestricts.rightInvOn := fun s hs => by
    rw [mem_quasispectrum_iff] at hs
    obtain (rfl | hs) := hs
    · simpa using hf 0
    · obtain ⟨r, rfl⟩ := h hs
      rw [hf r]
  left_inv := hf

