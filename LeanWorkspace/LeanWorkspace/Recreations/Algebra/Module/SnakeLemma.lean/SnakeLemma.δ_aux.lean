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

include hg hρ h₂ hσ hι₃ in
theorem SnakeLemma.δ_aux (x : K₃) : g₁ (ρ (i₂ (σ (ι₃ x)))) = i₂ (σ (ι₃ x)) := by
  obtain ⟨d, hd⟩ : i₂ (σ (ι₃ x)) ∈ range g₁ := by
    rw [← hg.linearMap_ker_eq, mem_ker, show g₂ (i₂ _) = i₃ (f₂ _) from DFunLike.congr_fun h₂ _,
      ← @comp_apply _ _ _ f₂ σ, hσ, id_eq, ← i₃.comp_apply,
      hι₃.linearMap_comp_eq_zero, zero_apply]
  rw [← hd, ← ρ.comp_apply, hρ, id_eq]

