import Mathlib

variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

theorem AffineMap.restrict.linear (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) :
    (φ.restrict hEF).linear = φ.linear.restrict (AffineMap.restrict.linear_aux hEF) := rfl

