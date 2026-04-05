import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem π_leftRightHomologyComparison_ι [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomologyπ ≫ S.leftRightHomologyComparison ≫ S.rightHomologyι =
      S.iCycles ≫ S.pOpcycles := CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι _ _

