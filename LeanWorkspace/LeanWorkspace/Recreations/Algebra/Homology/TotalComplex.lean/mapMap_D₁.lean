import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

variable [L.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
theorem mapMap_D₁ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₁ c₁₂ i₁₂ i₁₂' =
      K.D₁ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  cat_disch

