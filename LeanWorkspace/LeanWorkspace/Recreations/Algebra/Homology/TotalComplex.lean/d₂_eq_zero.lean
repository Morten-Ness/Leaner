import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

variable (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)

theorem d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [HomologicalComplex₂.d₂]
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

