import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_iff_epi_toCycles [S.HasHomology] : S.Exact ↔ Epi S.toCycles := S.leftHomologyData.exact_iff_epi_f'

