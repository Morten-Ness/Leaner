import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.mono_g_iff (hS : S.Exact) : Mono S.g ↔ S.f = 0 := by
  constructor
  · intro
    rw [← cancel_mono S.g, zero, zero_comp]
  · exact hS.mono_g

