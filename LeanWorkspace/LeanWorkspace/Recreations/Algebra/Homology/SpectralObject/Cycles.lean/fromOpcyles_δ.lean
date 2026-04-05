import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem fromOpcyles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.δ f₁ f₂₃ n₀ n₁ hn₁ =
      X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁  := by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀),
    p_fromOpcycles_assoc, CategoryTheory.Abelian.SpectralObject.pOpcycles_δFromOpcycles,
    X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁,
    Functor.map_id, Category.comp_id]

