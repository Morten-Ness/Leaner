import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem cyclesMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    CategoryTheory.ShortComplex.cyclesMap (0 : S₁ ⟶ S₂) = 0 := CategoryTheory.ShortComplex.cyclesMap'_zero _ _

