import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem D₂_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = - K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_neg, totalAux.ιMapObj_D₁_assoc]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [HomologicalComplex₂.totalAux.d₁_eq totalAux K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, HomologicalComplex₂.totalAux.ιMapObj_D₂ totalAux]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · have h₅ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next i₂) = i₁₂' := by
            rw [← c₁₂.next_eq' h₁, ← h, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄]
          have h₆ : ComplexShape.π c₁ c₂ c₁₂ (c₁.next i₁, c₂.next i₂) = i₁₂'' := by
            rw [← c₁₂.next_eq' h₂, ← ComplexShape.next_π₁ c₂ c₁₂ h₃, h₅]
          simp only [HomologicalComplex₂.totalAux.d₂_eq totalAux K c₁₂ _ h₄ _ h₅, HomologicalComplex₂.totalAux.d₂_eq totalAux K c₁₂ _ h₄ _ h₆,
            Linear.units_smul_comp, assoc, HomologicalComplex₂.totalAux.ιMapObj_D₁ totalAux, Linear.comp_units_smul,
            HomologicalComplex₂.totalAux.d₁_eq totalAux K c₁₂ h₃ _ _ h₆, HomologicalComplex.Hom.comm_assoc, smul_smul,
            ComplexShape.ε₂_ε₁ c₁₂ h₃ h₄, neg_mul, Units.neg_smul]
        · simp only [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp, comp_zero, smul_zero, neg_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp, neg_zero]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · rw [HomologicalComplex₂.totalAux.d₂_eq totalAux K c₁₂ i₁ h₄ i₁₂']; swap
          · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, ← c₁₂.next_eq' h₁, h]
          simp only [Linear.units_smul_comp, assoc, HomologicalComplex₂.totalAux.ιMapObj_D₁ totalAux]
          rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, comp_zero, smul_zero]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, K.D₂_shape c₁₂ _ _ h₂, comp_zero, comp_zero, neg_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, K.D₂_shape c₁₂ _ _ h₁, zero_comp, zero_comp, neg_zero]

