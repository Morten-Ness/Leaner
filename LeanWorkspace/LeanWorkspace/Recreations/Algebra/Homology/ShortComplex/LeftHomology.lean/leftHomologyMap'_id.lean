import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem leftHomologyMap'_id (h : S.LeftHomologyData) :
    CategoryTheory.ShortComplex.leftHomologyMap' (𝟙 S) h h = 𝟙 _ := CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq (LeftHomologyMapData.id h)

