import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem D₂_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₂ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [HomologicalComplex₂.totalAux.ιMapObj_D₂ totalAux, comp_zero]
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' c₁₂ i₁ h₂ i₁₂']
    intro h₁
    exact h₁₂ (by simpa only [← h, ← h₁] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂)
  · exact HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h₂

