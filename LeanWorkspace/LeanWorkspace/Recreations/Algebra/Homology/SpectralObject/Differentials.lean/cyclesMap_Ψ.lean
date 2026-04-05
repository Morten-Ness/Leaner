import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

include h₂₃ in
theorem cyclesMap_Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀ ≫
      X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ = 0 := by
  rw [← cancel_epi (X.toCycles f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) n₀), comp_zero,
    X.toCycles_cyclesMap_assoc f₁₂ f₃ f₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) f₂₃ h₂₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂)
    (twoδ₁Toδ₀ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])) n₀ rfl rfl,
    CategoryTheory.Abelian.SpectralObject.toCycles_Ψ .., zero₃_assoc .., zero_comp]

