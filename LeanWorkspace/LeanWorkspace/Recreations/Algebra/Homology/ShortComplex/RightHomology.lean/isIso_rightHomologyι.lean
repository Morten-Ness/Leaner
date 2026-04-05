import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [S.HasRightHomology]

theorem isIso_rightHomologyι (hg : S.g = 0) : IsIso S.rightHomologyι := RightHomologyData.isIso_ι _ hg

