import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.epi_toCycles (hS : S.Exact) [S.HasLeftHomology] : Epi S.toCycles := hS.epi_f' _

