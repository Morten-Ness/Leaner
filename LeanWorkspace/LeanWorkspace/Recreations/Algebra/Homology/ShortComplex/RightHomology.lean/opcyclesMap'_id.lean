import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesMap'_id (h : S.RightHomologyData) :
    CategoryTheory.ShortComplex.opcyclesMap' (𝟙 S) h h = 𝟙 _ := CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq (RightHomologyMapData.id h)

