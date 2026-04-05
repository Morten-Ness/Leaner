import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem D₁_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₁ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [HomologicalComplex₂.totalAux.ιMapObj_D₁ totalAux, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
    intro h₂
    exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
  · exact HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h₁

