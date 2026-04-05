import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

theorem ι_D₁ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i₁ i₂ i₁₂' := by
  apply HomologicalComplex₂.totalAux.ιMapObj_D₁ totalAux

