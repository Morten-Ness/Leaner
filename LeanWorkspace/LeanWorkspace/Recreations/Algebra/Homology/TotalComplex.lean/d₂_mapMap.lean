import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

variable [L.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem d₂_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₂ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · simp [HomologicalComplex₂.totalAux.d₂_eq' totalAux _ c₁₂ i₁ h]
  · simp [HomologicalComplex₂.d₂_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

