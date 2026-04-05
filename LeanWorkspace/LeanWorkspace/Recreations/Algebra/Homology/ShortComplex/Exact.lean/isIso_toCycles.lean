import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem isIso_toCycles (hS : S.Exact) [Mono S.f] [S.HasLeftHomology] :
    IsIso S.toCycles := CategoryTheory.ShortComplex.Exact.isIso_f' hS _

