import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

variable (S₁ S₂ : AffineSubspace k P₁) [Nonempty S₁] [Nonempty S₂]

theorem ofEq_symm (h : S₁ = S₂) : (AffineEquiv.ofEq S₁ S₂ h).symm = AffineEquiv.ofEq S₂ S₁ h.symm := by
  ext
  rfl

