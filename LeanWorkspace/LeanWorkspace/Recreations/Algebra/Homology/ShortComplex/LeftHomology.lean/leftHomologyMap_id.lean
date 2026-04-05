import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem leftHomologyMap_id [HasLeftHomology S] :
    CategoryTheory.ShortComplex.leftHomologyMap (𝟙 S) = 𝟙 _ := CategoryTheory.ShortComplex.leftHomologyMap'_id _

