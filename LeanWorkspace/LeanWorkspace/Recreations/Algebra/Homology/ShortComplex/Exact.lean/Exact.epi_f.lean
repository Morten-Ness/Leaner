import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.epi_f (hS : S.Exact) (hg : S.g = 0) : Epi S.f := by
  have := hS.hasHomology
  have := hS.mono_fromOpcycles
  have : S.pOpcycles = 0 := by rw [← cancel_mono S.fromOpcycles, zero_comp, p_fromOpcycles, hg]
  apply Preadditive.epi_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.p_descOpcycles x₂ hx₂, this, zero_comp]

