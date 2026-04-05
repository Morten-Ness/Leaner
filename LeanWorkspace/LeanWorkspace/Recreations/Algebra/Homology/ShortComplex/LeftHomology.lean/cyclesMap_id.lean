import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem cyclesMap_id [HasLeftHomology S] :
    CategoryTheory.ShortComplex.cyclesMap (𝟙 S) = 𝟙 _ := CategoryTheory.ShortComplex.cyclesMap'_id _

