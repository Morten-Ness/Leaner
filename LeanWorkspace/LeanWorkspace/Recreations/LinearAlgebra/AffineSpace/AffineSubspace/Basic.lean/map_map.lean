import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem map_map (s : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.map f).map g = s.map (g.comp f) := coe_injective <| image_image _ _ _

