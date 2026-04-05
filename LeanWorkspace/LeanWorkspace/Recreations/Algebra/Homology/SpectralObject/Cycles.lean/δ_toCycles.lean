import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem δ_toCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_mono (X.iCycles f₁ f₂ n₁), Category.assoc,
    CategoryTheory.Abelian.SpectralObject.toCycles_i, CategoryTheory.Abelian.SpectralObject.δToCycles_iCycles,
    ← X.δ_naturality f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) n₀ n₁,
    Functor.map_id, Category.id_comp]

