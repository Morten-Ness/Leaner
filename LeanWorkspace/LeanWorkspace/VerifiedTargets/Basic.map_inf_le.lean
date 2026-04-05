import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem map_inf_le (s₁ s₂ : AffineSubspace k P₁) : (s₁ ⊓ s₂).map f ≤ s₁.map f ⊓ s₂.map f := le_inf (AffineSubspace.map_mono _ inf_le_left) (AffineSubspace.map_mono _ inf_le_right)

