import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

variable {S₁ S₂ : AffineSubspace k P₁} [Nonempty S₁]

theorem inclusion_rfl : AffineSubspace.inclusion (le_refl S₁) = AffineMap.id k S₁ := rfl

