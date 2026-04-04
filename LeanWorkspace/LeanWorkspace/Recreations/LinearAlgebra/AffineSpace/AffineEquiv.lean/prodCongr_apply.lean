import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable (k P₁)

variable {k P₁}

variable (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₃ ≃ᵃ[k] P₄)

namespace Formalization

theorem prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) := rfl


end Formalization
