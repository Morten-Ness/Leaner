import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomologyMap'
    (h : S.HomologyData) (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ =
      leftHomologyMap' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ rightHomologyMap' (𝟙 S) h.right h₂ := by
  simpa only [h.leftRightHomologyComparison'_eq] using
    CategoryTheory.ShortComplex.leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right

