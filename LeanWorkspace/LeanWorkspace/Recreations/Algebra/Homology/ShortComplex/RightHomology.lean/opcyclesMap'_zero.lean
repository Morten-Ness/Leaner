import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    CategoryTheory.ShortComplex.opcyclesMap' 0 h₁ h₂ = 0 := CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq (RightHomologyMapData.zero h₁ h₂)

