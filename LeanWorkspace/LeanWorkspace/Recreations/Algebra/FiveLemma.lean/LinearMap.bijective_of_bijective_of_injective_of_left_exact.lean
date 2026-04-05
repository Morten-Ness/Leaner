import Mathlib

variable {R : Type*} [CommRing R]

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}

variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]

variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]

variable [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]

variable [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]

variable (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)

variable (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)

variable (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃) (i₄ : M₄ →ₗ[R] N₄)
  (i₅ : M₅ →ₗ[R] N₅)

variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)

variable (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)

variable (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)

include hf₁ hg₁ hc₁ hc₂ in
theorem bijective_of_bijective_of_injective_of_left_exact (hi₂ : Function.Bijective i₂)
    (hi₃ : Function.Injective i₃) (hf₀ : Function.Injective f₁) (hg₀ : Function.Injective g₁) :
    Function.Bijective i₁ := ⟨fun {x y} h ↦ (hf₀ (hi₂.1 (congr($hc₁ x).symm.trans (congr(g₁ $h).trans congr($hc₁ y))))),
    LinearMap.surjective_of_surjective_of_injective_of_left_exact f₁ f₂ g₁ g₂ i₁ i₂ i₃
      hc₁ hc₂ hf₁ hg₁ hi₂.2 hi₃ hg₀⟩

