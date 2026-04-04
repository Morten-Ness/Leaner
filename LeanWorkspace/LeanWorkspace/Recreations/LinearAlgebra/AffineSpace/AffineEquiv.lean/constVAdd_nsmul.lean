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

theorem constVAdd_nsmul (n : ℕ) (v : V₁) : AffineEquiv.constVAdd k P₁ (n • v) = AffineEquiv.constVAdd k P₁ v ^ n := (AffineEquiv.constVAddHom k P₁).map_pow _ _


end Formalization
