import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem p_fromOpcycles : S.pOpcycles ≫ S.fromOpcycles = S.g := S.rightHomologyData.p_g'

