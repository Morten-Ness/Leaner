import Mathlib

structure Formalization (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p

variable {k P₁ P₂ V₁ V₂ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

theorem toAffineMap_injective : Function.Injective (AffineEquiv.toAffineMap : (P₁ ≃ᵃ[k] P₂) → P₁ →ᵃ[k] P₂) := by
  exact AffineEquiv.toAffineMap_injective

namespace Formalization

theorem toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' :=
  toAffineMap_injective.eq_iff

end Formalization
