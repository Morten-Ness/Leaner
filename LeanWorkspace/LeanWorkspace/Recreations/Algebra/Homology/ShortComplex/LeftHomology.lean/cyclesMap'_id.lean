import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem cyclesMap'_id (h : S.LeftHomologyData) :
    CategoryTheory.ShortComplex.cyclesMap' (𝟙 S) h h = 𝟙 _ := CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq (LeftHomologyMapData.id h)

