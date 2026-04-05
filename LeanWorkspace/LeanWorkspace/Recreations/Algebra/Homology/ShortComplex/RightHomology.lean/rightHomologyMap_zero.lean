import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem rightHomologyMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    CategoryTheory.ShortComplex.rightHomologyMap (0 : S₁ ⟶ S₂) = 0 := CategoryTheory.ShortComplex.rightHomologyMap'_zero _ _

