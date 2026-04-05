import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

include h₁₂ in
theorem Ψ_opcyclesMap (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
      X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ = 0 := by
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) n₁),
    zero_comp, assoc, X.opcyclesMap_fromOpcycles f₁ f₂ f₁ f₂₃ f₁₂ h₁₂
    (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃)
    (twoδ₂Toδ₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃) (by rw [reassoc_of% h₁₂])) n₁ rfl rfl,
    Ψ_fromOpcycles_assoc .., zero₁ .., comp_zero]

