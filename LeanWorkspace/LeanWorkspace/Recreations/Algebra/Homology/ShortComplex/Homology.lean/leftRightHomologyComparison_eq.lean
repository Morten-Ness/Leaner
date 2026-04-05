import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem leftRightHomologyComparison_eq [S.HasLeftHomology] [S.HasRightHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    S.leftRightHomologyComparison = h₁.leftHomologyIso.hom ≫
      CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ h₂.rightHomologyIso.inv := CategoryTheory.ShortComplex.leftRightHomologyComparison'_compatibility _ _ _ _

