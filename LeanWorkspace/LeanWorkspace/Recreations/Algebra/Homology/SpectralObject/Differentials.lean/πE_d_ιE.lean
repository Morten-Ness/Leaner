import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

theorem πE_d_ιE
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (n₀ n₁ n₂ n₃ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ = X.Ψ f₂ f₃ f₄ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.toCycles f₃ f₄ _ rfl n₁ ), CategoryTheory.Abelian.SpectralObject.toCycles_Ψ ..,
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    πE_ιE .., toCycles_i_assoc, ← X.δ_naturality_assoc (f₁ ≫ f₂) (f₃ ≫ f₄) f₂ (f₃ ≫ f₄)
      (twoδ₁Toδ₀ f₁ f₂ _ rfl) (𝟙 _) n₁ n₂ rfl hn₂, Functor.map_id, id_comp]

