import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable {R : Type*} [CommRing R] [Module R V₁] [Module R V₂] [Module R V₃] [Module R V₄]

variable (e₁ : P₁ ≃ᵃ[R] P₂) (e₂ : P₃ ≃ᵃ[R] P₄)

theorem arrowCongr_apply (f : P₁ →ᵃ[R] P₃) (x : P₂) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl

