import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

namespace Formalization

theorem toAffineMap_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) :
    AffineEquiv.toAffineMap (AffineEquiv.mk f f' h) = ⟨f, f', h⟩ := rfl


end Formalization
