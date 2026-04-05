import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

theorem d_map_fourδ₄Toδ₃ (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃ = 0 := by
  simp [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂), ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃]

