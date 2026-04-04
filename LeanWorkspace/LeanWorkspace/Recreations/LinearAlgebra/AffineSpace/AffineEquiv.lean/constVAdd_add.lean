import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable (k P₁)

variable {k P₁}

variable (k)

variable (P₁)

namespace Formalization

theorem constVAdd_add (v w : V₁) :
    AffineEquiv.constVAdd k P₁ (v + w) = (AffineEquiv.constVAdd k P₁ w).trans (AffineEquiv.constVAdd k P₁ v) := AffineEquiv.ext <| add_vadd _ _


end Formalization
