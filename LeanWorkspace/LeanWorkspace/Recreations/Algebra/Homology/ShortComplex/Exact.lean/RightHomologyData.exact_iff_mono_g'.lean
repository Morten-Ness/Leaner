import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem RightHomologyData.exact_iff_mono_g' [S.HasHomology] (h : RightHomologyData S) :
    S.Exact ↔ Mono h.g' := by
  constructor
  · intro hS
    exact hS.mono_g' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

