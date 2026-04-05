import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem star_le_star_iff {x y : R} : star x ≤ star y ↔ x ≤ y := by
  suffices ∀ x y, x ≤ y → star x ≤ star y from
    ⟨by simpa only [star_star] using this (star x) (star y), this x y⟩
  intro x y h
  rw [StarOrderedRing.le_iff] at h ⊢
  obtain ⟨d, hd, rfl⟩ := h
  refine ⟨starAddEquiv d, ?_, star_add _ _⟩
  refine AddMonoidHom.mclosure_preimage_le _ _ <| AddSubmonoid.closure_mono ?_ hd
  rintro - ⟨s, rfl⟩
  exact ⟨s, by simp⟩

