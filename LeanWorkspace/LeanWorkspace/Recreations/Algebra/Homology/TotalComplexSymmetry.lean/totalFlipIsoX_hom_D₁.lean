import Mathlib

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

variable [K.HasTotal c] [DecidableEq J]

set_option backward.isDefEq.respectTransparency false in
theorem totalFlipIsoX_hom_D₁ (j j' : J) :
    (K.totalFlipIsoX c j).hom ≫ K.D₁ c j j' =
      K.flip.D₂ c j j' ≫ (K.totalFlipIsoX c j').hom := by
  by_cases h₀ : c.Rel j j'
  · ext i₂ i₁ h₁
    dsimp [HomologicalComplex₂.totalFlipIsoX]
    rw [ι_totalDesc_assoc, Linear.units_smul_comp, ι_D₁, ι_D₂_assoc]
    dsimp
    by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
    · have h₃ : ComplexShape.π c₂ c₁ c ⟨i₂, c₁.next i₁⟩ = j' := by
        rw [← ComplexShape.next_π₂ c₂ c i₂ h₂, h₁, c.next_eq' h₀]
      have h₄ : ComplexShape.π c₁ c₂ c ⟨c₁.next i₁, i₂⟩ = j' := by
        rw [← h₃, ComplexShape.π_symm c₁ c₂ c]
      rw [K.d₁_eq _ h₂ _ _ h₄, K.flip.d₂_eq _ _ h₂ _ h₃, Linear.units_smul_comp,
        assoc, ι_totalDesc, Linear.comp_units_smul, smul_smul, smul_smul,
        ComplexShape.σ_ε₁ c₂ c h₂ i₂]
      dsimp only [flip_X_X, flip_X_d]
    · rw [K.d₁_eq_zero _ _ _ _ h₂, K.flip.d₂_eq_zero _ _ _ _ h₂, smul_zero, zero_comp]
  · rw [K.D₁_shape _ _ _ h₀, K.flip.D₂_shape c _ _ h₀, zero_comp, comp_zero]

