import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem iCycles_g : S.iCycles ≫ S.g = 0 := S.leftHomologyData.wi

