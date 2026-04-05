import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasLeftHomology]

theorem isIso_leftHomologyπ (hf : S.f = 0) : IsIso S.leftHomologyπ := LeftHomologyData.isIso_π _ hf

