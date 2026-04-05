import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem leftHomologyMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    CategoryTheory.ShortComplex.leftHomologyMap' 0 h₁ h₂ = 0 := CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq (LeftHomologyMapData.zero h₁ h₂)

