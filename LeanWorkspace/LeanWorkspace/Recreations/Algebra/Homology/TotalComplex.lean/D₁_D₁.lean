import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem D₁_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₁_assoc, comp_zero]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [HomologicalComplex₂.totalAux.d₁_eq totalAux K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, HomologicalComplex₂.totalAux.ιMapObj_D₁ totalAux]
        by_cases h₄ : c₁.Rel (c₁.next i₁) (c₁.next (c₁.next i₁))
        · rw [HomologicalComplex₂.totalAux.d₁_eq totalAux K c₁₂ h₄ i₂ i₁₂'', Linear.comp_units_smul,
            d_f_comp_d_f_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₁ c₂ c₁₂ h₄, ← ComplexShape.next_π₁ c₂ c₁₂ h₃,
            h, c₁₂.next_eq' h₁, c₁₂.next_eq' h₂]
        · rw [K.d₁_eq_zero _ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, zero_comp]

