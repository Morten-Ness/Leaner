import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem interior_subset_closedInterior {n : ℕ} (s : Affine.Simplex k P n) :
    s.interior ⊆ s.closedInterior := fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩

