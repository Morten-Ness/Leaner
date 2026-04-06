FAIL
import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem interior_subset_closedInterior {n : ℕ} (s : Affine.Simplex k P n) :
    s.interior ⊆ s.closedInterior := by
  intro x hx
  rw [Affine.Simplex.interior] at hx
  rw [Affine.Simplex.closedInterior]
  exact Affine.Simplex.setInterior_mono (by
    intro y hy
    exact Set.Ioo_subset_Icc_self hy) hx
