import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem hasHomology_of_isIsoLeftRightHomologyComparison [S.HasLeftHomology]
    [S.HasRightHomology] [h : IsIso S.leftRightHomologyComparison] :
    S.HasHomology := by
  haveI : IsIso (CategoryTheory.ShortComplex.leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData) := h
  exact CategoryTheory.ShortComplex.hasHomology_of_isIso_leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData

