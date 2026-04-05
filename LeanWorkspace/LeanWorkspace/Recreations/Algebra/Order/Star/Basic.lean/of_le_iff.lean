import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R]

theorem of_le_iff (h_le_iff : ∀ x y : R, x ≤ y ↔ ∃ s, y = x + star s * s) : StarOrderedRing R where
  le_iff x y := by
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨p, hp⟩ := (h_le_iff x y).mp h
      exact ⟨star p * p, AddSubmonoid.subset_closure ⟨p, rfl⟩, hp⟩
    · rintro ⟨p, hp, hpxy⟩
      revert x y hpxy
      refine AddSubmonoid.closure_induction ?_ (fun x y h => add_zero x ▸ h.ge) ?_ hp
      · rintro _ ⟨s, rfl⟩ x y rfl
        exact (h_le_iff _ _).mpr ⟨s, rfl⟩
      · rintro _ _ _ _ ha hb x y rfl
        rw [← add_assoc]
        exact (ha _ _ rfl).trans (hb _ _ rfl)

