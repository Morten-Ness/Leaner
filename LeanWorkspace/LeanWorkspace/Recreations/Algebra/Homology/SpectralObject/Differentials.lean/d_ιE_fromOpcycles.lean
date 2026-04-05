import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅)
  (n₀ n₁ n₂ n₃ : ℤ)

include h₃₄ in
theorem d_ιE_fromOpcycles
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫ X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂ =
      X.ιE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₄ f₅ f₄₅ h₄₅ n₁ ≫
        X.δ f₂₃ f₄₅ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    πE_ιE_assoc .., p_fromOpcycles, toCycles_i_assoc, fromOpcyles_δ ..,
    πE_ιE_assoc .., pOpcycles_δFromOpcycles, toCycles_i_assoc, ← Functor.map_comp, Eq.comm]
  apply δ_naturality
  simp

