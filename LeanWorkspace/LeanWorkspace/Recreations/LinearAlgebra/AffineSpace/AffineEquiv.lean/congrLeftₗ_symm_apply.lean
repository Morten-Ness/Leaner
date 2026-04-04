import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable (R W : Type*) [Ring R] [AddCommGroup W] [Module k W] [Module R W] [SMulCommClass k R W]
  (e : P₁ ≃ᵃ[k] P₂)

namespace Formalization

theorem congrLeftₗ_symm_apply (f : P₂ →ᵃ[k] W) (x : P₁) : (e.congrLeftₗ R W).symm f x = f (e x) := rfl


end Formalization
