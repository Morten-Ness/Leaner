import Mathlib

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

variable [K.HasTotal c] [DecidableEq J]

set_option backward.isDefEq.respectTransparency false in
theorem ιTotal_totalFlipIso_f_hom
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₂ c₁ c (i₂, i₁) = j) :
    K.flip.ιTotal c i₂ i₁ j h ≫ (K.totalFlipIso c).hom.f j =
      ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]) := by
  simp [HomologicalComplex₂.totalFlipIso, HomologicalComplex₂.totalFlipIsoX]

