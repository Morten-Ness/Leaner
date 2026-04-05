import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem leftRightHomologyComparison_fac [S.HasHomology] :
    S.leftRightHomologyComparison = S.leftHomologyIso.hom ≫ S.rightHomologyIso.inv := by
  simpa only [CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    CategoryTheory.ShortComplex.RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using
      CategoryTheory.ShortComplex.leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

