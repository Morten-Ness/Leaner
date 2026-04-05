import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.mono_g (hS : S.Exact) (hf : S.f = 0) : Mono S.g := by
  have := hS.hasHomology
  have := hS.epi_toCycles
  have : S.iCycles = 0 := by rw [← cancel_epi S.toCycles, comp_zero, toCycles_i, hf]
  apply Preadditive.mono_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.liftCycles_i x₂ hx₂, this, comp_zero]

