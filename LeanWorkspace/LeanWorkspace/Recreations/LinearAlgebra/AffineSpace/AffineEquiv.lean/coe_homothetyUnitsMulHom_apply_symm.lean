import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable (k P₁)

variable {k P₁}

variable (k)

variable (P₁)

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

namespace Formalization

theorem coe_homothetyUnitsMulHom_apply_symm (p : P) (t : Rˣ) :
    ((AffineEquiv.homothetyUnitsMulHom p t).symm : P → P) = AffineMap.homothety p (↑t⁻¹ : R) := rfl


end Formalization
