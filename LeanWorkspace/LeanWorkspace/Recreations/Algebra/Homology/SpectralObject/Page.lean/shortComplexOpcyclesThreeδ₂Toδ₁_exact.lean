import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
    (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

set_option backward.isDefEq.respectTransparency false in
theorem shortComplexOpcyclesThreeδ₂Toδ₁_exact
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  let φ : X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂) :=
    { τ₁ := X.pOpcycles f₁ f₂₃ n₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, X.p_opcyclesMap _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂)] }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂

