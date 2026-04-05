import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem δToCycles_iCycles (hn₁ : n₀ + 1 = n₁) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.iCycles f₁ f₂ n₁ =
      X.δ f₂ f₃ n₀ n₁ hn₁ := by
  simp only [CategoryTheory.Abelian.SpectralObject.δToCycles, CategoryTheory.Abelian.SpectralObject.liftCycles_i]

