import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesMap_id [HasRightHomology S] :
    CategoryTheory.ShortComplex.opcyclesMap (𝟙 S) = 𝟙 _ := CategoryTheory.ShortComplex.opcyclesMap'_id _

