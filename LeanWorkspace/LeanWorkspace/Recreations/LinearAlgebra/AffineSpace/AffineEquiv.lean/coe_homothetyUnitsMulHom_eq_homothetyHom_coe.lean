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

theorem coe_homothetyUnitsMulHom_eq_homothetyHom_coe (p : P) :
    ((↑) : (P ≃ᵃ[R] P) → P →ᵃ[R] P) ∘ AffineEquiv.homothetyUnitsMulHom p =
      AffineMap.homothetyHom p ∘ ((↑) : Rˣ → R) := funext fun _ => rfl

