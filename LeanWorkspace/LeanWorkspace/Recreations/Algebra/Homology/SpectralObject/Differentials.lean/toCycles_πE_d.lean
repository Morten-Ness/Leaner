import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅)
  (n₀ n₁ n₂ n₃ : ℤ)

theorem toCycles_πE_d
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.toCycles f₃ f₄ f₃₄ h₃₄ n₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
        X.δ f₁₂ f₃₄ n₁ n₂ hn₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₂ ≫
          X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  subst h₁₂ h₃₄
  simp only [CategoryTheory.Abelian.SpectralObject.d, δ_toCycles_assoc, toCycles_πE_descE]

