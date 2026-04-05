import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem toCycles_Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂₃ n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁ := by
  subst h₂₃
  simp only [CategoryTheory.Abelian.SpectralObject.Ψ, toCycles_descCycles]

