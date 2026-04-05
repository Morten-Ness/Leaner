import Mathlib

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

variable [K.HasTotal c] [DecidableEq J]

theorem totalFlipIso_hom_f_D₁ (j j' : J) :
    (K.totalFlipIso c).hom.f j ≫ K.D₁ c j j' =
      K.flip.D₂ c j j' ≫ (K.totalFlipIso c).hom.f j' := by
  apply HomologicalComplex₂.totalFlipIsoX_hom_D₁

