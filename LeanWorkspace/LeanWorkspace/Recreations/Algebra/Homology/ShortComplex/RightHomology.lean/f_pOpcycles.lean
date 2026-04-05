import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem f_pOpcycles : S.f ≫ S.pOpcycles = 0 := S.rightHomologyData.wp

