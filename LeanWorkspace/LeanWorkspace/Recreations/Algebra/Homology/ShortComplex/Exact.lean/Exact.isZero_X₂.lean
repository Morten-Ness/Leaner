import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.isZero_X₂ (hS : S.Exact) (hf : S.f = 0) (hg : S.g = 0) : IsZero S.X₂ := by
  have := hS.mono_g hf
  rw [IsZero.iff_id_eq_zero, ← cancel_mono S.g, hg, comp_zero, comp_zero]

