import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.epi_f_iff (hS : S.Exact) : Epi S.f ↔ S.g = 0 := by
  constructor
  · intro
    rw [← cancel_epi S.f, zero, comp_zero]
  · exact hS.epi_f

