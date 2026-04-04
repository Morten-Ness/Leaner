import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem map_eq_bot_iff {s : AffineSubspace k P₁} : s.map f = ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← coe_eq_bot_iff, AffineSubspace.coe_map, image_eq_empty, coe_eq_bot_iff] at h
  · rw [h, AffineSubspace.map_bot]

