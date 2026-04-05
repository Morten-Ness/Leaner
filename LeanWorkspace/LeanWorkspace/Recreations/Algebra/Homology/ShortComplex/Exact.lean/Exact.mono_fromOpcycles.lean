import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.mono_fromOpcycles (hS : S.Exact) [S.HasRightHomology] : Mono S.fromOpcycles := hS.mono_g' _

