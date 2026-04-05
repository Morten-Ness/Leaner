import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem hasHomology_of_isIso_leftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂)] :
    S.HasHomology := CategoryTheory.ShortComplex.HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

