import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ ≠ i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [HomologicalComplex₂.totalAux.d₂_eq' totalAux K c₁₂ i₁ h i₁₂, K.toGradedObject.ιMapObjOrZero_eq_zero, comp_zero, smul_zero]
  exact h'

