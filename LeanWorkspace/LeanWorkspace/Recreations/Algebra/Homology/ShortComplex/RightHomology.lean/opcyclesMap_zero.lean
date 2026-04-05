import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem opcyclesMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    CategoryTheory.ShortComplex.opcyclesMap (0 : S₁ ⟶ S₂) = 0 := CategoryTheory.ShortComplex.opcyclesMap'_zero _ _

