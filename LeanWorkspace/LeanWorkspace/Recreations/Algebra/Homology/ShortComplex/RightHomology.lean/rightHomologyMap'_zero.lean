import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    CategoryTheory.ShortComplex.rightHomologyMap' 0 h₁ h₂ = 0 := CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq (RightHomologyMapData.zero h₁ h₂)

