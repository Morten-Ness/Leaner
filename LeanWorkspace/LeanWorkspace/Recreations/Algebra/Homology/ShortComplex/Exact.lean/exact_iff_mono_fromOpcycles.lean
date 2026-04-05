import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem exact_iff_mono_fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycles := S.rightHomologyData.exact_iff_mono_g'

