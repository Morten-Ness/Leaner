import Mathlib

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

theorem flip_hasTotal_iff : K.flip.HasTotal c ↔ K.HasTotal c := by
  constructor
  · intro
    change K.flip.flip.HasTotal c
    have := TotalComplexShapeSymmetry.symmetry c₁ c₂ c
    infer_instance
  · intro
    infer_instance

