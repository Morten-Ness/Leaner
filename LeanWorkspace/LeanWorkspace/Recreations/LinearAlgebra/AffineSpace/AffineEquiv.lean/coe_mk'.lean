import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

namespace Formalization

theorem coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(AffineEquiv.mk' e e' p h) = e := rfl


end Formalization
