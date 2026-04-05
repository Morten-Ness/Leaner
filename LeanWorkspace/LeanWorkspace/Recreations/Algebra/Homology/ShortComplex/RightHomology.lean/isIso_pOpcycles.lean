import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem isIso_pOpcycles (hf : S.f = 0) : IsIso S.pOpcycles := RightHomologyData.isIso_p _ hf

