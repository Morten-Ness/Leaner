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

theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P₁}
    (h : Function.Injective (2 • · : V₁ → V₁)) : AffineEquiv.pointReflection k x y = y ↔ y = x := Equiv.pointReflection_fixed_iff_of_injective_two_nsmul h

