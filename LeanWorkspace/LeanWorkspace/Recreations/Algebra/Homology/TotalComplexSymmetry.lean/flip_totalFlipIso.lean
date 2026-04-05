import Mathlib

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

variable [K.HasTotal c] [DecidableEq J]

variable [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c]

theorem flip_totalFlipIso : K.flip.totalFlipIso c = (K.totalFlipIso c).symm := by
  ext j i₁ i₂ h
  rw [Iso.symm_hom, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  dsimp only [flip_flip]
  rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_inv, ComplexShape.σ_symm]

