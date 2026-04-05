import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem isIso_g' (hS : S.Exact) (h : S.RightHomologyData) [Epi S.g] :
    IsIso h.g' := by
  have := hS.mono_g' h
  have := epi_of_epi_fac h.p_g'
  exact isIso_of_mono_of_epi h.g'

