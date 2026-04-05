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

include hπ₂ in
theorem SnakeLemma.exact_δ_left (G : C₁ →ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Function.Surjective π₁) :
    Exact (δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁) G := by
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨x, rfl⟩ := h x
    obtain ⟨y, hy⟩ := (hπ₂ (g₁ x)).mp (by simpa only [← LinearMap.comp_apply, hF] using H)
    obtain ⟨z, hz⟩ : f₂ y ∈ range ι₃ := (hι₃ (f₂ y)).mp (by rw [← i₃.comp_apply, ← h₂,
      g₂.comp_apply, hy, hg.apply_apply_eq_zero])
    exact ⟨z, δ_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ _ _ hz.symm _ hy.symm⟩
  · rintro ⟨x, rfl⟩
    simp only [δ, coe_mk, AddHom.coe_mk]
    rw [← G.comp_apply, hF, π₂.comp_apply, H₂, hπ₂.apply_apply_eq_zero]

