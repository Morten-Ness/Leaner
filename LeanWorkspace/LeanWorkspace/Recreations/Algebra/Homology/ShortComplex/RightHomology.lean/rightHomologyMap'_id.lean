import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap'_id (h : S.RightHomologyData) :
    CategoryTheory.ShortComplex.rightHomologyMap' (𝟙 S) h h = 𝟙 _ := CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq (RightHomologyMapData.id h)

