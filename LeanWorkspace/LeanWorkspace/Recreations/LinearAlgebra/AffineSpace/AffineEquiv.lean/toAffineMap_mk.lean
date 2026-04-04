import Mathlib

variable {k P₁ P₂ V₁ V₂ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

namespace Formalization

theorem toAffineMap_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂)
    (h : ∀ (p : P₁) (v : V₁), f (v +ᵥ p) = f' v +ᵥ f p) :
    AffineEquiv.toAffineMap (AffineEquiv.mk f f' h) = ⟨f, f', h⟩ :=
  rfl

end Formalization
