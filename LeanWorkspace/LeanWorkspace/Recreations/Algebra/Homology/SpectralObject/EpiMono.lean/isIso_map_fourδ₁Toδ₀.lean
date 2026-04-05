import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

theorem isIso_map_fourδ₁Toδ₀ (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert (inferInstance : Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert (inferInstance : IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h

