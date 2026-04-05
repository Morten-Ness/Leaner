import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem isIso_fromOpcycles (hS : S.Exact) [Epi S.g] [S.HasRightHomology] :
    IsIso S.fromOpcycles := CategoryTheory.ShortComplex.Exact.isIso_g' hS _

