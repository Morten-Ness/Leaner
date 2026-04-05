import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem isIso_iCycles (hg : S.g = 0) : IsIso S.iCycles := LeftHomologyData.isIso_i _ hg

