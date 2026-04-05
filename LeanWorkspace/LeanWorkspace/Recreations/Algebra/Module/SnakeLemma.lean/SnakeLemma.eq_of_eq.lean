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

include hf h₁ hρ hπ₁ in
theorem SnakeLemma.eq_of_eq (x : K₃)
    (y₁) (hy₁ : f₂ y₁ = ι₃ x) (z₁) (hz₁ : g₁ z₁ = i₂ y₁)
    (y₂) (hy₂ : f₂ y₂ = ι₃ x) (z₂) (hz₂ : g₁ z₂ = i₂ y₂) : π₁ z₁ = π₁ z₂ := by
  have := sub_eq_zero.mpr (hy₁.trans hy₂.symm)
  rw [← map_sub, hf] at this
  obtain ⟨d, hd⟩ := this
  rw [← eq_sub_iff_add_eq.mp hd, map_add, ← hz₂, ← sub_eq_iff_eq_add, ← map_sub,
    ← i₂.comp_apply, ← h₁, LinearMap.comp_apply,
    (HasLeftInverse.injective ⟨ρ, congr_fun hρ⟩).eq_iff] at hz₁
  rw [← sub_eq_zero, ← map_sub, hz₁, hπ₁]
  exact ⟨_, rfl⟩

