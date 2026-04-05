import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem sequenceΨ_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sequenceΨ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).Exact :=
  exact_of_δ₀ (X.cyclesMap_Ψ_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows
    (X.Ψ_opcyclesMap_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows

