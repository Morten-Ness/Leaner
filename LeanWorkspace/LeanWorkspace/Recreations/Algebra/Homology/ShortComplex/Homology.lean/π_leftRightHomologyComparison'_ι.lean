import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)

theorem π_leftRightHomologyComparison'_ι :
    h₁.π ≫ CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι = h₁.i ≫ h₂.p := by
  simp only [CategoryTheory.ShortComplex.leftRightHomologyComparison'_eq_liftH,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]

