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

include hι₂ in
theorem SnakeLemma.exact_δ_right (F : K₂ →ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F)
    (h : Function.Injective ι₃) :
    Exact F (δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁) := by
  haveI H₁ : ∀ x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨y, hy⟩ := (hπ₁ _).mp H
    obtain ⟨k, hk⟩ : σ (ι₃ x) - f₁ y ∈ Set.range ι₂ := by
      rw [← hι₂, map_sub, ← H₂, ← hy, sub_eq_zero]; exact congr($h₁ y)
    refine ⟨k, h ?_⟩
    rw [← ι₃.comp_apply, ← hF, f₂.comp_apply, hk, map_sub, H₁, hf.apply_apply_eq_zero, sub_zero]
  · rintro ⟨y, rfl⟩
    exact (δ_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ _ (ι₂ y) congr($hF y)
      _ (by rw [map_zero, hι₂.apply_apply_eq_zero])).trans π₁.map_zero

