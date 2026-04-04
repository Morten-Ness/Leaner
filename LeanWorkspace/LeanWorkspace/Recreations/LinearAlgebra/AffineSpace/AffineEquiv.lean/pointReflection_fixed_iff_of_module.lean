import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable (k P₁)

variable {k P₁}

variable (k)

variable (P₁)

variable {P₁}

namespace Formalization

theorem pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} :
    AffineEquiv.pointReflection k x y = y ↔ y = x := ((AffineEquiv.injective_pointReflection_left_of_module k y).eq_iff' (AffineEquiv.pointReflection_self k y)).trans eq_comm


end Formalization
