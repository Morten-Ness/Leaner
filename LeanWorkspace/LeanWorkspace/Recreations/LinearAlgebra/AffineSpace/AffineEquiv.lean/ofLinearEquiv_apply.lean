import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable {k V P : Type*}

variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem ofLinearEquiv_apply (A : V ≃ₗ[k] V) (p₀ p₁ : P) (x : P) :
    AffineEquiv.ofLinearEquiv A p₀ p₁ x = A (x -ᵥ p₀) +ᵥ p₁ := rfl

