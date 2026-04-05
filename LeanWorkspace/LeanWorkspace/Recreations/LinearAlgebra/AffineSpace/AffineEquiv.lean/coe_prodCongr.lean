import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₃ ≃ᵃ[k] P₄)

theorem coe_prodCongr :
    (e₁.prodCongr e₂ : P₁ × P₃ →ᵃ[k] P₂ × P₄) = (e₁ : P₁ →ᵃ[k] P₂).prodMap (e₂ : P₃ →ᵃ[k] P₄) := rfl

