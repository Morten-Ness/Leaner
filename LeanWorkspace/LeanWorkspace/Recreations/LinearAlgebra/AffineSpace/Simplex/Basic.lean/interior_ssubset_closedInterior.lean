import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem interior_ssubset_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Affine.Simplex k P n) :
    s.interior ⊂ s.closedInterior := by
  rw [Set.ssubset_iff_exists]
  exact ⟨s.interior_subset_closedInterior, s.points 0, s.point_mem_closedInterior 0,
    s.point_notMem_interior 0⟩

