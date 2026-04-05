import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem isIso_f' (hS : S.Exact) (h : S.LeftHomologyData) [Mono S.f] :
    IsIso h.f' := by
  have := hS.epi_f' h
  have := mono_of_mono_fac h.f'_i
  exact isIso_of_mono_of_epi h.f'

