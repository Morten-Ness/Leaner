import Mathlib

variable {R : Type*} [CommRing R] {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
  (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃)
  (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (hf : Exact f₁ f₂)
  (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (hg : Exact g₁ g₂)
  (h₁ : g₁.comp i₁ = i₂.comp f₁) (h₂ : g₂.comp i₂ = i₃.comp f₂)
  (σ : M₃ → M₂) (hσ : f₂ ∘ σ = id) (ρ : N₂ → N₁) (hρ : ρ ∘ g₁ = id)
  {K₂ K₃ C₁ C₂ : Type*} [AddCommGroup K₂] [Module R K₂] [AddCommGroup K₃] [Module R K₃]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  (ι₂ : K₂ →ₗ[R] M₂) (hι₂ : Exact ι₂ i₂) (ι₃ : K₃ →ₗ[R] M₃) (hι₃ : Exact ι₃ i₃)
  (π₁ : N₁ →ₗ[R] C₁) (hπ₁ : Exact i₁ π₁) (π₂ : N₂ →ₗ[R] C₂) (hπ₂ : Exact i₂ π₂)

theorem SnakeLemma.δ_eq (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y) :
    δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ x = π₁ z := eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ x _ (congr_fun hσ _) _
    (δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃ _) y hy z hz

