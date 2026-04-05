import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem toCycles_i : S.toCycles ≫ S.iCycles = S.f := S.leftHomologyData.f'_i

