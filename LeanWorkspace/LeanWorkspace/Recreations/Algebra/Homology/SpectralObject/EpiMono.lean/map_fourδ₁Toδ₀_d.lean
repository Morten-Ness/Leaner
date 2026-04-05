import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

theorem map_fourδ₁Toδ₀_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ = 0 := by
  simp [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂),
    X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃, X.map_ιE_assoc
    f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by cat_disch) hn₁ hn₂]

