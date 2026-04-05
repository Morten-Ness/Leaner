import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
  (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

theorem πE_EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ := by
  simpa [← cancel_mono (X.iCycles f₁ f₂₃ n₁)] using (X.cyclesMap_i ..).symm

