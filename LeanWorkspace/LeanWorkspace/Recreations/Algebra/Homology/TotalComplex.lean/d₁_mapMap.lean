import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

variable [L.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem d₁_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₁ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · simp [HomologicalComplex₂.totalAux.d₁_eq' totalAux _ c₁₂ h]
  · simp [HomologicalComplex₂.d₁_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

