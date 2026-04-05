import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem pOpcycles_δFromOpcycles (hn₁ : n₀ + 1 = n₁) :
    X.pOpcycles f₂ f₃ n₀ ≫ X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂ n₀ n₁ hn₁ := by
  simp only [CategoryTheory.Abelian.SpectralObject.δFromOpcycles, CategoryTheory.Abelian.SpectralObject.p_descOpcycles]

