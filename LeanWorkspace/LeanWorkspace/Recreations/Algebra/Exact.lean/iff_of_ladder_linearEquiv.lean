import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem iff_of_ladder_linearEquiv
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Function.Exact g₁₂ g₂₃ ↔ Function.Exact f₁₂ f₂₃ := iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)

