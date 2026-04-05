import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

variable [L.HasTotal c₁₂]

variable [M.HasTotal c₁₂]

theorem map_comp : HomologicalComplex₂.total.map (φ ≫ ψ) c₁₂ = HomologicalComplex₂.total.map φ c₁₂ ≫ HomologicalComplex₂.total.map ψ c₁₂ := by
  apply (HomologicalComplex.forget _ _).map_injective
  exact GradedObject.mapMap_comp (toGradedObjectMap φ) (toGradedObjectMap ψ) _

