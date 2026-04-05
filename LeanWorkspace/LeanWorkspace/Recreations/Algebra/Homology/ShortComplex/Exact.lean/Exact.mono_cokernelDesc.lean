import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.mono_cokernelDesc [S.HasHomology] [HasCokernel S.f] (hS : S.Exact) :
    Mono (Limits.cokernel.desc S.f S.g S.zero) := S.exact_iff_mono_cokernel_desc.1 hS

