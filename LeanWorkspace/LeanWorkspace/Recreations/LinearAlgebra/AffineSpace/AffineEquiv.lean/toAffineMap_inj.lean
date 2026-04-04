import Mathlib

variable {k P₁ P₂ V₁ V₂ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

theorem toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' :=
  AffineEquiv.toAffineMap_injective.eq_iff
