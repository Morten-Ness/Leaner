import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
    (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

theorem opcyclesMap_threeδ₂Toδ₁_opcyclesToE
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesMap _ _ _ _ (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) n₁ ≫
      X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  rw [← cancel_epi (X.pOpcycles ..), comp_zero,
    p_opcyclesMap_assoc _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)]
  simp

