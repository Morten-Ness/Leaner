import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap_id [HasRightHomology S] :
    CategoryTheory.ShortComplex.rightHomologyMap (𝟙 S) = 𝟙 _ := CategoryTheory.ShortComplex.rightHomologyMap'_id _

