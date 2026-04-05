import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

variable [L.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem ιTotal_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ (HomologicalComplex₂.total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotal c₁₂ i₁ i₂ i₁₂ h := by
  simp [HomologicalComplex₂.total.map, HomologicalComplex₂.ιTotal]

